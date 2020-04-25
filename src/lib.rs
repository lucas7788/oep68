#![cfg_attr(not(feature = "mock"), no_std)]
#![feature(proc_macro_hygiene)]
extern crate ontio_std as ostd;
use ostd::abi::Error::IrregularData;
use ostd::abi::{Decoder, Encoder, Error, EventBuilder, Sink, Source};
use ostd::contract::{ong, ont};
use ostd::database;
use ostd::prelude::*;
use ostd::runtime;
use ostd::types::u128_to_neo_bytes;
use ostd::types::{Address, U128};

const ADMIN: Address = ostd::macros::base58!("AbtTQJYKfQxq4UdygDsbLVjE8uRrJ2H3tP");
const ONG_CONTRACT_ADDRESS: Address = ostd::macros::base58!("AFmseVrdL9f9oyCzZefL9tG6UbvhfRZMHJ");
const ONT_CONTRACT_ADDRESS: Address = ostd::macros::base58!("AFmseVrdL9f9oyCzZefL9tG6UbvhUMqNMV");

const NEO: &[u8] = b"neo";
const WASM: &[u8] = b"wasm";
const KEY_TOKEN: &[u8] = b"01";
const KEY_NEXT_STREAM_ID: &[u8] = b"02";
const KEY_STREAM: &[u8] = b"03";
const KEY_PROXY: &[u8] = b"04";
const KEY_MIGRATE: &[u8] = b"05";

#[derive(Encoder, Decoder)]
struct Stream {
    stream_id: U128,
    from: Address,     // the payer
    to: Address,       // the receiver
    amount: U128,      // the total money to be streamed
    token: Address,    // the token address to be streamed
    start_time: U128,  // the unix timestamp for when the stream starts
    stop_time: U128,   // the unix timestamp for when the stream stops
    transferred: U128, // has transferred to to_address
}

struct Token {
    token_address: Address,
    vm_ty: VmType,
}

impl<'a> Decoder<'a> for Token {
    fn decode(source: &mut Source<'a>) -> Result<Self, Error> {
        Ok(Token {
            token_address: source.read()?,
            vm_ty: VmType(source.read_byte()?),
        })
    }
}

impl Encoder for Token {
    fn encode(&self, sink: &mut Sink) {
        sink.write(&self.token_address);
        sink.write(self.vm_ty.0);
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct VmType(u8);

const NEO_VM: VmType = VmType(0u8);
const WASM_VM: VmType = VmType(1u8);

impl<'a> Decoder<'a> for VmType {
    fn decode(source: &mut Source<'a>) -> Result<Self, Error> {
        let buf: &[u8] = source.read()?;
        if buf == NEO {
            return Ok(NEO_VM);
        } else if buf == WASM {
            return Ok(WASM_VM);
        }
        Err(IrregularData)
    }
}

fn register_token(token_address: &Address, vm_ty: VmType) -> bool {
    assert!(vm_ty == NEO_VM || vm_ty == WASM_VM);
    assert!(runtime::check_witness(&ADMIN));
    let mut tokens = get_registered_token();
    if has_registered_token(&tokens, token_address) {
        return false;
    }
    tokens.push(Token {
        token_address: token_address.clone(),
        vm_ty: vm_ty,
    });
    database::put(KEY_TOKEN, tokens);
    true
}

fn delete_token(token_addr: Address) -> bool {
    assert!(runtime::check_witness(&ADMIN));
    let mut tokens = get_registered_token();
    let index = tokens
        .iter()
        .position(|x| x.token_address == token_addr)
        .unwrap();
    tokens.swap_remove(index);
    true
}

fn add_migrate(from: &Address, to: Address) -> bool {
    assert!(runtime::check_witness(&ADMIN));
    database::put(utils::gen_migrate_key(from), to);
    true
}

fn get_migrate(from: &Address) -> Address {
    let mut from_mut = from.clone();
    while let Some(temp) = database::get::<_, Address>(utils::gen_migrate_key(&from_mut)) {
        from_mut = temp;
    }
    from_mut
}

fn get_registered_token() -> Vec<Token> {
    database::get(KEY_TOKEN).unwrap_or_default()
}

fn create_stream(
    from: Address,
    to: Address,
    amount: U128,
    token: Address,
    start_time: U128,
    stop_time: U128,
) -> bool {
    if !check_registered_token(&token) {
        return false;
    }
    assert!(runtime::check_witness(&from));
    let cur_contract_addr = runtime::address();
    let empty_addr = Address::repeat_byte(0);
    assert!(amount != 0 && &to != &cur_contract_addr && &to != &empty_addr);
    let now = runtime::timestamp();
    assert!(start_time >= now as U128 && start_time < stop_time);
    assert!(transfer(&token, &from, &cur_contract_addr, amount));
    let stream_id = get_next_stream_id();
    let stream = Stream {
        stream_id,
        from,
        to,
        amount,
        token,
        start_time,
        stop_time,
        transferred: 0,
    };
    database::put(utils::gen_stream_key(stream_id), stream);
    update_stream_id(stream_id + 1);
    EventBuilder::new()
        .string("create_stream")
        .number(stream_id)
        .address(&from)
        .address(&to)
        .number(amount)
        .address(&token)
        .number(start_time)
        .number(stop_time)
        .notify();
    true
}

fn balance_of(stream_id: U128, addr: &Address) -> U128 {
    if let Some(stream) = get_stream(stream_id) {
        let mut cur_time: U128 = runtime::timestamp() as U128;
        if cur_time < stream.start_time {
            cur_time = stream.start_time;
        } else if cur_time > stream.stop_time {
            cur_time = stream.stop_time
        }
        let mul_val = (stream.amount as u128)
            .checked_mul((cur_time - stream.start_time) as u128)
            .unwrap();
        let div_val = mul_val
            .checked_div(stream.stop_time - stream.start_time)
            .unwrap();
        let to_balance = div_val.checked_sub(stream.transferred).unwrap_or_default();
        if &stream.from == addr {
            return stream.amount - stream.transferred - to_balance;
        } else if &stream.to == addr {
            return to_balance;
        }
    }
    0
}

fn withdraw_from_stream(stream_id: U128) -> bool {
    if let Some(mut stream) = get_stream(stream_id) {
        if let Some(proxy) = get_proxy() {
            assert!(runtime::check_witness(&stream.to) || runtime::check_witness(&proxy));
        } else {
            assert!(runtime::check_witness(&stream.to));
        }
        let self_addr = runtime::address();
        let cur_time = runtime::timestamp();
        assert!(cur_time >= stream.start_time as u64 && cur_time <= stream.stop_time as u64);
        let should_transfer_amt: U128 = balance_of(stream_id, &stream.to);
        assert!(transfer(
            &stream.token,
            &self_addr,
            &stream.to,
            should_transfer_amt
        ));
        stream.transferred += should_transfer_amt;
        database::put(utils::gen_stream_key(stream_id), &stream);
        EventBuilder::new()
            .string("withdraw_from_stream")
            .number(stream_id)
            .address(&stream.to)
            .number(should_transfer_amt)
            .notify();
        return true;
    }
    false
}

fn cancel_stream(stream_id: U128) -> bool {
    if let Some(mut stream) = get_stream(stream_id) {
        assert!(runtime::check_witness(&stream.to) || runtime::check_witness(&stream.from));
        let self_addr = runtime::address();
        let from_balance = balance_of(stream_id, &stream.from);
        let to_balance = balance_of(stream_id, &stream.to);
        assert!(transfer(
            &stream.token,
            &self_addr,
            &stream.from,
            from_balance
        ));
        assert!(transfer(&stream.token, &self_addr, &stream.to, to_balance));
        stream.transferred += from_balance;
        stream.transferred += to_balance;
        database::put(utils::gen_stream_key(stream_id), &stream);
        EventBuilder::new()
            .string("cancel_stream")
            .number(stream_id)
            .address(&stream.from)
            .address(&stream.to)
            .number(from_balance)
            .number(to_balance)
            .notify();
        return true;
    }
    false
}

fn set_proxy(addr: Address) -> bool {
    assert!(runtime::check_witness(&ADMIN));
    database::put(KEY_PROXY, addr.clone());
    EventBuilder::new()
        .string("set_proxy")
        .address(&addr)
        .notify();
    true
}
fn get_proxy() -> Option<Address> {
    database::get::<_, Address>(KEY_PROXY)
}

fn get_stream(id: U128) -> Option<Stream> {
    database::get::<_, Stream>(utils::gen_stream_key(id))
}

fn transfer(token: &Address, from: &Address, to: &Address, amount: U128) -> bool {
    if token == &ONG_CONTRACT_ADDRESS {
        return ong::transfer(from, to, amount);
    } else if token == &ONT_CONTRACT_ADDRESS {
        return ont::transfer(from, to, amount);
    }
    let token_new = get_migrate(token);
    let ty = get_vm_ty(&token_new);
    match ty {
        NEO_VM => {
            return transfer_neo(token, from, to, amount);
        }
        WASM_VM => {}
        _ => panic!(""),
    }
    false
}
fn transfer_neo(token: &Address, from: &Address, to: &Address, amount: U128) -> bool {
    let mut sink = Sink::new(16);
    sink.write(0u8); // version
    sink.write(0x10u8); // list type
    sink.write(2u32);

    sink.write(01u8); //string type
    sink.write("transfer".len() as u32);
    sink.write(b"transfer");

    sink.write(0x10u8); // list type

    sink.write(3u32); // param length

    sink.write(2u8); //address type
    sink.write(from);

    sink.write(2u8);
    sink.write(to);

    sink.write(4u8); //u128
    sink.write(amount);
    let res = runtime::call_contract(&token, sink.bytes());
    if let Some(data) = res {
        if !data.is_empty() {
            EventBuilder::new().bytearray(data.as_slice()).notify();
            return true;
        }
    }
    return false;
}

fn balance_of_neo(addr: &Address) -> U128 {
    let mut sink = Sink::new(16);
    sink.write(0u8); // version
    sink.write(0x10u8); // list type
    sink.write(2u32);

    sink.write(01u8); //string type
    sink.write("balance_of".len() as u32);
    sink.write(b"balance_of");

    sink.write(0x10u8); // list type

    sink.write(1u32); // param length

    sink.write(2u8); //address type
    sink.write(addr);
    let res = runtime::call_contract(addr, sink.bytes());
    if let Some(data) = res {
        if !data.is_empty() {
            let mut source = Source::new(data.as_slice());
            let val: U128 = source.read().unwrap_or_default();
            return val;
        }
    }
    return 0;
}

fn check_registered_token(token_addr: &Address) -> bool {
    let tokens = get_registered_token();
    if has_registered_token(&tokens, token_addr) {
        return true;
    }
    false
}

fn update_stream_id(id: U128) {
    database::put(KEY_NEXT_STREAM_ID, id)
}
fn get_next_stream_id() -> U128 {
    let id = database::get(KEY_STREAM_ID).unwrap_or(1);
    database::put(KEY_STREAM_ID, id + 1);
    id
}

fn get_vm_ty(token_addr: &Address) -> VmType {
    let tokens = get_registered_token();
    for token in tokens.iter() {
        if &token.token_address == token_addr {
            return token.vm_ty.clone();
        }
    }
    VmType(2)
}

fn has_registered_token(addrs: &[Token], addr: &Address) -> bool {
    addrs.iter().any(|item| item.token_address == addr)
}

#[no_mangle]
pub fn invoke() {
    let input = runtime::input();
    let mut source = Source::new(&input);
    let action: &[u8] = source.read().unwrap();
    let mut sink = Sink::new(12);
    match action {
        b"transferNeo" => {
            let (token, from, to, amount) = source.read().unwrap();
            sink.write(transfer_neo(token, from, to, amount));
        }
        b"setProxy" => {
            let addr = source.read().unwrap();
            sink.write(set_proxy(addr));
        }
        b"getProxy" => {
            if let Some(addr) = get_proxy() {
                sink.write(addr)
            }
        }
        b"registerToken" => {
            let (token_address, token_ty) = source.read().unwrap();
            sink.write(register_token(token_address, token_ty));
        }
        b"getRegisteredToken" => {
            sink.write(get_registered_token());
        }
        b"unRegisterToken" => {
            let token_addr = source.read().unwrap();
            sink.write(delete_token(token_addr));
        }
        b"addMigrate" => {
            let (old_token, new_token) = source.read().unwrap();
            sink.write(add_migrate(old_token, new_token));
        }
        b"createStream" => {
            let (from, to, amount, token, start_time, stop_time) = source.read().unwrap();
            sink.write(create_stream(
                from, to, amount, token, start_time, stop_time,
            ));
        }
        b"getStream" => {
            let id = source.read().unwrap();
            if let Some(stream) = get_stream(id) {
                sink.write(stream);
            }
        }
        b"balanceOf" => {
            let (stream_id, addr) = source.read().unwrap();
            sink.write(balance_of(stream_id, addr));
        }
        b"withdrawFromStream" => {
            let stream_id = source.read().unwrap();
            sink.write(withdraw_from_stream(stream_id));
        }
        b"cancelStream" => {
            let stream_id = source.read().unwrap();
            sink.write(cancel_stream(stream_id));
        }
        _ => panic!("unsupported action!"),
    }
    runtime::ret(sink.bytes())
}

mod utils {
    use super::*;
    use ostd::types::u128_to_neo_bytes;
    pub fn gen_stream_key(id: U128) -> Vec<u8> {
        [KEY_STREAM, u128_to_neo_bytes(id).as_slice()].concat()
    }
    pub fn gen_migrate_key(from: &Address) -> Vec<u8> {
        [KEY_MIGRATE, from.as_ref()].concat()
    }
}

#[cfg(test)]
mod tests {
    extern crate ontio_std as ostd;
    use crate::ostd::abi::Decoder;
    use hexutil::to_hex;
    use ostd::abi::{Sink, Source};
    use ostd::contract::contract_mock::NeoCommand;
    use ostd::mock::build_runtime;
    use ostd::prelude::*;
    use ostd::types::{Address, H256};
    use std::collections::HashMap;
    #[test]
    fn test_new() {
        let addr = Address::repeat_byte(1);
        let handle = build_runtime();
        handle.witness(&[crate::ADMIN]);
        assert!(crate::set_proxy(addr.clone()));
        assert_eq!(crate::get_proxy().unwrap(), addr);

        let token_address = crate::ONG_CONTRACT_ADDRESS;
        assert!(crate::register_token(&token_address, crate::NEO_VM));
        assert_eq!(crate::get_registered_token().len(), 1);

        let token = Address::repeat_byte(2);
        let token2 = Address::repeat_byte(3);
        assert!(crate::add_migrate(&token, token2.clone()));
        assert_eq!(crate::get_migrate(&token), token2.clone());
        let token3 = Address::repeat_byte(4);
        assert!(crate::add_migrate(&token2, token3.clone()));
        assert_eq!(crate::get_migrate(&token), token3);
    }

    #[test]
    fn test_create_stream() {
        let token = Address::repeat_byte(16);
        let from = Address::repeat_byte(1);
        let to = Address::repeat_byte(2);
        let handle = build_runtime();
        handle.witness(&[crate::ADMIN]);
        assert!(crate::register_token(&token, crate::NEO_VM));

        let mut ong_balance_map = HashMap::<Address, U128>::new();
        ong_balance_map.insert(from.clone(), 10000);
        ong_balance_map.insert(to.clone(), 10000);

        let call_contract = move |_addr: &Address, _data: &[u8]| -> Option<Vec<u8>> {
            let mut sink = Sink::new(12);
            let mut source = Source::new(_data);
            println!("{}", to_hex(_data));
            let command = NeoCommand::decode(&mut source).ok().unwrap();
            match command {
                NeoCommand::Transfer { from, to, value } => {
                    let mut from_ba = ong_balance_map.get(from).map(|val| val.clone()).unwrap();
                    let mut to_ba = ong_balance_map
                        .get(to)
                        .map(|val| val.clone())
                        .unwrap_or_default();
                    from_ba -= value;
                    to_ba += value;
                    ong_balance_map.insert(from.clone(), from_ba);
                    ong_balance_map.insert(to.clone(), to_ba);
                    sink.write(true);
                }
                NeoCommand::BalanceOf { addr } => {
                    let ba = ong_balance_map.get(addr).map(|val| val.clone()).unwrap();
                    sink.write(ba);
                }
                _ => {}
            }
            return Some(sink.bytes().to_vec());
        };
        let contract_addr = Address::repeat_byte(20);
        handle.address(&contract_addr);
        handle.on_contract_call(call_contract);
        handle.timestamp(1);
        handle.witness(&[&from]);
        assert!(crate::create_stream(
            from.clone(),
            to.clone(),
            100,
            token,
            10,
            20
        ));

        assert_eq!(crate::balance_of(1, &from), 100);
        assert_eq!(crate::balance_of(1, &to), 0);
        assert_eq!(crate::balance_of_neo(&from), 10000 - 100);
        assert_eq!(crate::balance_of_neo(&contract_addr), 100);

        handle.timestamp(15);
        assert_eq!(crate::balance_of(1, &from), 50);
        assert_eq!(crate::balance_of(1, &to), 50);

        handle.timestamp(21);
        assert_eq!(crate::balance_of(1, &from), 0);
        assert_eq!(crate::balance_of(1, &to), 100);

        handle.witness(&[&to]);
        handle.timestamp(15);
        assert!(crate::withdraw_from_stream(1));
        assert_eq!(crate::balance_of_neo(&contract_addr), 50);
        assert_eq!(crate::balance_of_neo(&to), 10000 + 50);
        assert_eq!(crate::balance_of(1, &from), 50);
        assert_eq!(crate::balance_of(1, &to), 0);

        assert!(crate::cancel_stream(1));
        assert_eq!(crate::balance_of(1, &from), 0);
        assert_eq!(crate::balance_of(1, &to), 0);
        assert_eq!(crate::balance_of_neo(&contract_addr), 0);
        assert_eq!(crate::balance_of_neo(&to), 10000 + 50);
        assert_eq!(crate::balance_of_neo(&from), 10000 - 100 + 50);
    }
}
