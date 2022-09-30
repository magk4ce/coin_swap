address 0x02{
    module GoldCoin{
        
        use 0x2::BaseCoin;
        struct GoldCoin has drop{ }

        public fun mint(to:address, amount:u64){
            BaseCoin::mint<GoldCoin>(to,amount);
        }
        public fun transfer(addr:address,to:address,amount:u64){
            BaseCoin::transfer<GoldCoin>(addr,to,amount);
        }

        public fun init_balance(account:&signer){
            BaseCoin::init_balance<GoldCoin>(account);
        }

        
    }
}