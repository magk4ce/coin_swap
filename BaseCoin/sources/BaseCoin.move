address 0x2{
// ---------------------------base_coin moduel----------------------
    module BaseCoin{
        use std::signer;
        use std::error;

        const MODULE_OWNER:address=@0x6;
        
        const E_NOT_MODULE_OWNER:u64=1000;
        const E_BALANCE_EXISTS:u64=1001;
        const E_BALANCE_NOT_EXIST:u64=1002;
        const E_COIN_EXHAUSTED:u64=1003;
        const E_SAME_ADDR:u64=1003;


        struct Coin<phantom CoinType> has store{
            amount:u64
        }
        struct Balance<phantom CoinType> has key{
            coin:Coin<CoinType>
        }

        public fun balance_of<CoinType>(addr:address):u64 acquires Balance{
            let coin =& borrow_global<Balance<CoinType>>(addr).coin;
            coin.amount
        }
        
        public fun init_balance<CoinType>(account: &signer) {
            let addr=signer::address_of(account);
            assert!(!exists<Balance<CoinType>>(addr),error::already_exists(E_BALANCE_EXISTS));
            let emp_coin=Coin<CoinType>{amount:0};
            move_to(account,Balance{coin:emp_coin });
        }

        public fun token_exists<CoinType:drop>(addr:address):bool {
            exists<Balance<CoinType>>(addr)
        }

        public fun mint<CoinType: drop>( mint_to:address,amount: u64) acquires Balance {
            // debug::print(&mint_to);
            assert!(exists<Balance<CoinType>>(mint_to),error::not_found(E_BALANCE_NOT_EXIST));
            let coin=Coin<CoinType>{amount};
            deposit(mint_to,coin);
        }

        public fun burn<CoinType: drop>(account:&signer, amount: u64, _witness: CoinType) acquires Balance {
            let addr=signer::address_of(account);
            assert!(exists<Balance<CoinType>>(addr),error::not_found(E_BALANCE_NOT_EXIST));
            let coin = withdraw<CoinType>(addr,amount);
            let Coin{amount:_}=coin;
        }

        spec burn{
            let coin = & borrow_global<Balance<CoinType>>(burn_addr).coin;
            let value=coin.amount;
            let post vl= & borrow_global<Balance<CoinType>>(burn_addr).coin.value;
            aborts_if value < amount;
            ensures amount == vl-value;
        }

        public fun transfer<CoinType: drop>(addr: address, to: address, amount: u64) acquires Balance {
            let value=balance_of<CoinType>(addr);
            assert!((value >= amount),error::resource_exhausted(E_COIN_EXHAUSTED));
            let coin=withdraw<CoinType>(addr,amount);
            deposit(to,coin);
        }
        spec transfer{
            let addr=signer::address_of(account);
            include Transfer_schema<CoinType>{addr,to_addr:to,amount};
        }
         spec schema Transfer_schema<CoinType>{
             addr:address;
             to_addr:address;
             amount:u64;

            aborts_if !exists<Balance>(addr);
            aborts_if !exists<Balance>(to_addr);

            let from_value=balance_of(addr);
            let to_value=balance_of(to_addr);
            let post from_value_post = balance_of(addr);
            let post to_value_post = to_value_post=balance_of(to_addr);
            ensures (from_value - from_value_post) == amount;
            ensures (to_value_post - to_value) == amount;

             }
        public fun withdraw<CoinType: drop>(addr:address,amount:u64):Coin<CoinType> acquires Balance{
            assert!( exists<Balance<CoinType>>(addr),error::not_found(E_BALANCE_NOT_EXIST));
            let coin=&mut borrow_global_mut<Balance<CoinType>>(addr).coin;
            assert!((coin.amount >= amount),error::resource_exhausted(E_COIN_EXHAUSTED));
            coin.amount=coin.amount - amount;
            Coin<CoinType>{amount}
        }
        spec withdraw{
            let addr=signer::address_of(account);
            let value=balance_of(addr);
            let post value_post=balance_of(addr);
            ensures (value - value_post) == amount;
        }
        public fun deposit<CoinType: drop>(addr:address,check:Coin<CoinType>)acquires Balance{
            assert!( exists<Balance<CoinType>>(addr),error::not_found(E_BALANCE_NOT_EXIST));
            let coin = &mut borrow_global_mut<Balance<CoinType>>(addr).coin;
            let Coin{amount}=check;
            coin.amount=coin.amount + amount;
        }

        spec deposit{
            let addr=signer::address_of(account);
            let value=balance_of(addr);
            let post value_post=balance_of(addr);
            ensures ( value_post - value) == amount;
        }
        
    }

// // ---------------------------test moduel----------------------

//     module test{
//             use 0x2::base_coin::init_balance;
//             use 0x2::base_coin::mint;
//             use 0x2::base_coin::transfer;
//             use 0x2::base_coin::deposit;
//             use 0x2::base_coin::burn;
//             use 0x2::base_coin::balance_of;
//             use std::vector;
//             use std::string;
//             use std::debug;

//             #[test(owner=@0x6, add1=@0x2,add2=@0x3, add3=@0x4)]
//             fun test_funs(owner:&signer,add1:address,signer1:&signer,add2:address,signer2:&signer,add3:address,signer3:&signer){
//                 mint(owner,add1,10,Coin{});
//                 debug::print(balance_of(add1));
//             }
//     }


}
