address 0x02{
    module SilverCoin{
        
        use 0x2::BaseCoin;
        struct SilverCoin has drop{ }

        public fun mint(to:address, amount:u64){
            BaseCoin::mint<SilverCoin>(to,amount);
        }
        public fun transfer(addr:address,to:address,amount:u64){
            BaseCoin::transfer<SilverCoin>(addr,to,amount);
        }

        public fun init_balance(account:&signer){
            BaseCoin::init_balance<SilverCoin>(account);
        }
    }
}