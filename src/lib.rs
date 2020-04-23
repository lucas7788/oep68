#![cfg_attr(not(feature = "mock"), no_std)]
#![feature(proc_macro_hygiene)]
extern crate ontio_std as ostd;
use ostd::abi::Error::UnexpectedEOF;
use ostd::abi::{Decoder, Encoder, Error, EventBuilder, Sink, Source};
use ostd::contract::{ong, ont};
use ostd::database;
use ostd::prelude::*;
use ostd::runtime;
use ostd::types::u128_to_neo_bytes;
use ostd::types::{Address, U128};

const ADMIN: Address = ostd::macros::base58!("AXdmdzbyf3WZKQzRtrNQwAR91ZxMUfhXkt");
const ONG_CONTRACT_ADDRESS: Address = ostd::macros::base58!("AFmseVrdL9f9oyCzZefL9tG6UbvhfRZMHJ");
const ONT_CONTRACT_ADDRESS: Address = ostd::macros::base58!("AFmseVrdL9f9oyCzZefL9tG6UbvhUMqNMV");

const NEO: &[u8] = b"neo";
const WASM: &[u8] = b"wasm";
const KEY_TOKEN: &[u8] = b"01";
const KEY_STREAM_ID: &[u8] = b"02";
const KEY_STREAM: &[u8] = b"03";
const KEY_PROXY: &[u8] = b"04";
const KEY_MIGRATE: &[u8] = b"05";

#[derive(Encoder, Decoder)]
struct Stream {
    stream_id: U128,
    from: Address,        // the payer
    to: Address,          // the receiver
    amount: U128,         // the total money to be streamed
    token: Address,       // the token address to be streamed
    start_time: U128,     // the unix timestamp for when the stream starts
    stop_time: U128,      // the unix timestamp for when the stream stops
    transfered_amt: U128, // has transfered to to_address
}

struct Token {
    token_address: Address,
    token_ty: VmType,
}

impl<'a> Decoder<'a> for Token {
    fn decode(source: &mut Source<'a>) -> Result<Self, Error> {
        Ok(Token {
            token_address: source.read()?,
            token_ty: VmType(source.read_byte()?),
        })
    }
}

impl Encoder for Token {
    fn encode(&self, sink: &mut Sink) {
        sink.write(&self.token_address);
        sink.write(self.token_ty.0);
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct VmType(u8);

const NeoVm: VmType = VmType(0);
const WasmVm: VmType = VmType(1);

impl<'a> Decoder<'a> for VmType {
    fn decode(source: &mut Source<'a>) -> Result<Self, Error> {
        let buf: &[u8] = source.read().unwrap();
        if buf == NEO {
            return Ok(NeoVm);
        } else if buf == WASM {
            return Ok(WasmVm);
        }
        Err(UnexpectedEOF)
    }
}

fn register_token(token_address: &Address, vmTy: VmType) -> bool {
    if vmTy.0 != NeoVm.0 && vmTy.0 != WasmVm.0 {
        return false;
    }
    assert!(runtime::check_witness(&ADMIN));
    let mut tokens = get_registered_token();
    if has_registered_token(&tokens, token_address) {
        return false;
    }
    tokens.push(Token {
        token_address: token_address.clone(),
        token_ty: vmTy,
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
    tokens.remove(index);
    true
}

fn add_migrate(from: &Address, to: Address) -> bool {
    assert!(runtime::check_witness(&ADMIN));
    database::put(utils::gen_migrate_key(from), to);
    true
}

fn get_migrate(from: &Address) -> Address {
    let mut from_mut = from.clone();
    loop {
        if let Some(temp) = database::get::<_, Address>(utils::gen_migrate_key(&from_mut)) {
            from_mut = temp
        } else {
            break;
        }
    }
    from_mut
}

fn get_registered_token() -> Vec<Token> {
    if let Some(tokens) = database::get::<_, Vec<Token>>(KEY_TOKEN) {
        return tokens;
    }
    vec![]
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
    assert!(amount != 0 && to != from);
    let now = runtime::timestamp();
    assert!(start_time as u64 >= now && start_time < stop_time);
    let self_addr = runtime::address();
    assert!(transfer(&token, &from, &self_addr, amount));
    let stream_id = get_stream_id();
    let stream = Stream {
        stream_id,
        from,
        to,
        amount,
        token,
        start_time,
        stop_time,
        transfered_amt: 0,
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
        let to_balance = (cur_time - stream.start_time) as U128
            * (stream.amount - stream.transfered_amt)
            / (stream.stop_time - stream.start_time);
        if &stream.from == addr {
            return stream.amount - stream.transfered_amt - to_balance;
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
        stream.transfered_amt += should_transfer_amt;
        database::put(KEY_STREAM, &stream);
        EventBuilder::new()
            .string("withdraw_from_stream")
            .number(stream_id)
            .address(&stream.to)
            .number(stream.amount)
            .notify();
        return true;
    }
    false
}

fn cancel_stream(stream_id: U128) -> bool {
    if let Some(stream) = get_stream(stream_id) {
        assert!(runtime::check_witness(&stream.to) || runtime::check_witness(&stream.from));
        let self_addr = runtime::address();
        let from_balance = balance_of(stream_id, &stream.from);
        let to_balance = balance_of(stream_id, &stream.from);
        assert!(transfer(
            &stream.token,
            &self_addr,
            &stream.from,
            from_balance
        ));
        assert!(transfer(
            &stream.token,
            &self_addr,
            &stream.from,
            to_balance
        ));
        EventBuilder::new()
            .string("cancel_stream")
            .address(&stream.from)
            .address(&stream.to)
            .number(stream_id)
            .number(from_balance)
            .number(to_balance)
            .notify();
        return true;
    }
    false
}

fn set_proxy(addr: Address) -> bool {
    assert!(runtime::check_witness(&ADMIN));
    database::put(KEY_PROXY, addr);
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
    let ty = get_token_ty(&token_new);
    match ty {
        NeoVm => {
            let mut sink = Sink::new(16);
            sink.write(u128_to_neo_bytes(amount));
            sink.write_neovm_address(to);
            sink.write_neovm_address(from);
            sink.write(83u8);
            sink.write(193u8);
            sink.write("transfer".to_string());
            sink.write(103u8);
            sink.write(token);
            let res = runtime::call_contract(&token_new, sink.bytes());
            if let Some(data) = res {
                let mut source = Source::new(&data);
                return source.read().unwrap();
            } else {
                return false;
            }
        }
        WasmVm => {}
        _ => panic!(""),
    }
    false
}

fn check_registered_token(token_addr: &Address) -> bool {
    let tokens = get_registered_token();
    if has_registered_token(&tokens, token_addr) {
        return true;
    }
    false
}

fn update_stream_id(id: U128) {
    database::put(KEY_STREAM_ID, id)
}
fn get_stream_id() -> U128 {
    if let Some(id) = database::get::<_, U128>(KEY_STREAM_ID) {
        return id;
    }
    1
}

fn get_token_ty(token_addr: &Address) -> VmType {
    let tokens = get_registered_token();
    for token in tokens.iter() {
        if &token.token_address == token_addr {
            return token.token_ty.clone();
        }
    }
    VmType(2)
}

fn has_registered_token(addrs: &[Token], addr: &Address) -> bool {
    for item in addrs.iter() {
        if &item.token_address == addr {
            return true;
        }
    }
    false
}

#[no_mangle]
pub fn invoke() {
    let input = runtime::input();
    let mut source = Source::new(&input);
    let action = source.read().unwrap();
    let mut sink = Sink::new(12);
    match action {
        "set_proxy" => {
            let addr = source.read().unwrap();
            sink.write(set_proxy(addr));
        }
        "get_proxy" => {
            if let Some(addr) = get_proxy() {
                sink.write(addr)
            }
        }
        "register_token" => {
            let (token_address, token_ty) = source.read().unwrap();
            sink.write(register_token(token_address, token_ty));
        }
        "get_registered_token" => {
            sink.write(get_registered_token());
        }
        "delete_token" => {
            let token_addr = source.read().unwrap();
            sink.write(delete_token(token_addr));
        }
        "add_migrate" => {
            let (old_token, new_token) = source.read().unwrap();
            sink.write(add_migrate(old_token, new_token));
        }
        "create_stream" => {
            let (from, to, amount, token, start_time, stop_time) = source.read().unwrap();
            sink.write(create_stream(
                from, to, amount, token, start_time, stop_time,
            ));
        }
        "get_stream" => {
            let id = source.read().unwrap();
            if let Some(stream) = get_stream(id) {
                sink.write(stream);
            }
        }
        "balance_of" => {
            let (stream_id, addr) = source.read().unwrap();
            sink.write(balance_of(stream_id, addr));
        }
        "withdraw_from_stream" => {
            let stream_id = source.read().unwrap();
            sink.write(withdraw_from_stream(stream_id));
        }
        "cancel_stream" => {
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
    use ostd::abi::{Sink, Source};
    use ostd::mock::build_runtime;
    use ostd::prelude::*;
    use ostd::types::{Address, H256};
    #[test]
    fn test_new() {
        let addr = Address::repeat_byte(1);
        let handle = build_runtime();
        handle.witness(&[crate::ADMIN]);
        assert!(crate::set_proxy(addr.clone()));
        assert_eq!(crate::get_proxy().unwrap(), addr);

        let token_address = crate::ONG_CONTRACT_ADDRESS;
        assert!(crate::register_token(&token_address, crate::NeoVm));
        assert_eq!(crate::get_registered_token().len(), 1);

        let token = Address::repeat_byte(2);
        let token2 = Address::repeat_byte(3);
        assert!(crate::add_migrate(&token, token2.clone()));
        assert_eq!(crate::get_migrate(&token), token2.clone());
        let token3 = Address::repeat_byte(4);
        assert!(crate::add_migrate(&token2, token3.clone()));
        assert_eq!(crate::get_migrate(&token), token3);
    }
}
