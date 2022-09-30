address 0x2{

    module swap_coin{
        use std::signer;
        use 0x2::pair;
        use 0x2::BaseCoin;

        const MODULE_OWNER:address =@0x6;
        const E_NOT_MODULE_OWNER:u64=1000;
        const E_BALANCE_EXISTS:u64=1001;
        const E_PAIR_NOT_EXISTS:u64=1002;
        const AMOUNT_MUTIPLIER:u64 = 100000000000;

        public entry fun swap_coin<TokenA:drop,TokenB:drop,LPToken:drop> (account:&signer,amountA:u64){
            let addr=signer::address_of(account);
            // transfer coinA to owner_address
            BaseCoin::transfer<TokenA>(addr,MODULE_OWNER,amountA);
            let amountB = pair::calcu_amountB<TokenA,TokenB>(amountA);

            //transfer coinB to requester
            BaseCoin::transfer<TokenB>(MODULE_OWNER,addr,amountB);
            //update pair amount
            pair::update_pool<TokenA,TokenB>(amountA,amountB);

            // pay transfer fee (in TokenA)
            let fee = pair::calcl_fee<TokenA,TokenB>(amountA);
            if (fee == 0) return;
            // calculate current (TokenA -> LPToken) price
            let price = pair::est_price<TokenA,LPToken>(fee)/AMOUNT_MUTIPLIER;
            BaseCoin::transfer<LPToken>(addr,MODULE_OWNER,fee*price);

            // update fee in this pair
            pair::collect_fee<TokenA,TokenB>(fee);
        }
        spec swap_coin{
            let addr=signer::address_of(account);
            let am=BaseCoin::balance_of<TokenA>(addr);
            aborts_if am < amountA;
            let poolA= BaseCoin::balance_of<TokenA>(MODULE_OWNER);
            let post poolA_post = BaseCoin::balance_of<TokenA>(MODULE_OWNER);
            ensures poolA_post - poolA == amountA;
        }
    
    }

    module pair{

        use std::signer;
        use std::error;
        use std::debug;
        use 0x2::BaseCoin;
        friend 0x2::swap_coin;
        const MODULE_OWNER:address =@0x6;
        const AMOUNT_MUTIPLIER:u64 = 100000000000;
        const E_NOT_MODULE_OWNER:u64=1000;
        const E_BALANCE_EXISTS:u64=1001;
        const E_PAIR_NOT_EXISTS:u64=1002;
        const E_LIQUID_NOT_CORRECT:u64=1003;
        const E_PARAMETER_ERROR:u64 = 1004;

        
        struct Pair<phantom TokenA,phantom TokenB> has store,key{
            amountA:u64,
            amountB:u64,
            fee_rate:u64,
            fee:u64,
        }

        struct LPToken has drop{ }

         // only module owner could create pairs
        public entry fun init_pair<TokenA,TokenB>(account:&signer,fee_rate:u64){
                move_to(account,Pair<TokenA,TokenB>{
                    amountA:0,
                    amountB:0,
                    fee_rate,
                    fee:0,
                });
            }

        fun increase_pool<TokenA,TokenB>(staker:address,amountA:u64,amountB:u64) acquires Pair{
            let pool_pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            // update general pool amount
            pool_pair.amountA=pool_pair.amountA+amountA;
            pool_pair.amountB=pool_pair.amountB+amountB;

            // update lp pool amount
            let staker_pair=borrow_global_mut<Pair<TokenA,TokenB>>(staker);
            staker_pair.amountA=staker_pair.amountA+amountA;
            staker_pair.amountB=staker_pair.amountB+amountB;
        }
         fun decrease_pool<TokenA,TokenB>(addr:address,amountA:u64,amountB:u64) acquires Pair{
            let pair=borrow_global_mut<Pair<TokenA,TokenB>>(addr);
            // update general pool amount
            pair.amountA=pair.amountA-amountA;
            pair.amountB=pair.amountB-amountB;
            
        }
       public fun update_pool<TokenA,TokenB>(amountA:u64,amountB:u64) acquires Pair{
            let pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            pair.amountA=pair.amountA-amountA;
            pair.amountB=pair.amountB+amountB;
        }


        // add a pair of liquid
        public entry fun add_liquid<TokenA:drop,TokenB:drop,LPToken:drop>(account:&signer,amountA:u64,amountB:u64) acquires Pair{
            assert!(exists<Pair<TokenA,TokenB>>(MODULE_OWNER),error::not_found(E_PAIR_NOT_EXISTS));
            let addr=signer::address_of(account);
            let pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            if (pair.amountA != 0){assert!((pair.amountA * AMOUNT_MUTIPLIER / pair.amountB == amountA * AMOUNT_MUTIPLIER / amountB),error::invalid_argument(E_LIQUID_NOT_CORRECT));};

            // transfer cions to module_owner
            BaseCoin::transfer<TokenA>(addr,MODULE_OWNER,amountA);
            BaseCoin::transfer<TokenB>(addr,MODULE_OWNER,amountB);
            if (!exists<Pair<TokenA,TokenB>>(addr)){init_pair<TokenA,TokenB>(account,0)};
            if (!BaseCoin::token_exists<LPToken>(addr)){BaseCoin::init_balance<LPToken>(account)};

            increase_pool<TokenA,TokenB>(addr,amountA,amountB);

            // mint lptoken to general pool
            BaseCoin::mint<LPToken>(MODULE_OWNER,amountA);
            


        }
        spec add_liquid{
            // check pool is currect
            let pair=borrow_global<Pair<TokenA,TokenB>>(MODULE_OWNER);
            let post pair_post=borrow_global<Pair<TokenA,TokenB>>(MODULE_OWNER);
            ensures pair_post.amountA -  pair.amountA == amountA;
            ensures pair_post.amountB -  pair.amountB == amountB;

            // check the change of  cions amount is correct.
            let coinA_amount=borrow_global<TokenA>(addr);
            let coinB_amount=borrow_global<TokenB>(addr);
            let post coinA_amount_post=borrow_global<TokenA>(addr);
            let post coinB_amount_post=borrow_global<TokenB>(addr);
            ensures coinA_amount_post - coinA_amount == amountA;
            ensures coinB_amount_post - coinB_amount == amountB;
       
        }
       
        // remove percentage of liquid based on lp's pool
        public entry fun remove_liquid<TokenA:drop,TokenB:drop,LPToken:drop>(account:&signer,percentage:u64) acquires Pair{
            assert!(exists<Pair<TokenA,TokenB>>(MODULE_OWNER),error::not_found(E_PAIR_NOT_EXISTS));
            assert!(percentage <= 100,E_PARAMETER_ERROR);
            let addr=signer::address_of(account);
            

            let lp_pair = borrow_global_mut<Pair<TokenA,TokenB>>(addr);
            let amountA = percentage * lp_pair.amountA / 100 ;
            let amountB = percentage * lp_pair.amountB / 100 ;

            // transfer tokens to lp
            BaseCoin::transfer<TokenA>(MODULE_OWNER,addr,amountA);
            BaseCoin::transfer<TokenB>(MODULE_OWNER,addr,amountB);

            // update lp pool
            decrease_pool<TokenA,TokenB>(addr,amountA,amountB);
            
            // update general pool
            let pool_pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            let pool_amount = pool_pair.amountA;
            let pool_fee = pool_pair.fee;

            // transfer lptoken to lp
            BaseCoin::transfer<LPToken>(MODULE_OWNER, addr,amountA*pool_fee / pool_amount);

            // decrease general pool
            decrease_pool<TokenA,TokenB>(MODULE_OWNER,amountA,amountB);

        }

        spec remove_liquid{
            // check pool is currect
            let pair=borrow_global<Pair<TokenA,TokenB>>(MODULE_OWNER);
            let post pair_post=borrow_global<Pair<TokenA,TokenB>>(MODULE_OWNER);
            ensures pair.amountA -  pair_post.amountA == amountA;
            ensures pair.amountB -  pair_post.amountB == amountB;

            // check the change of  cions amount is correct.
            let coinA_amount=borrow_global<TokenA>(addr);
            let coinB_amount=borrow_global<TokenB>(addr);
            let post coinA_amount_post=borrow_global<TokenA>(addr);
            let post coinB_amount_post=borrow_global<TokenB>(addr);
            ensures coinA_amount - coinA_amount_post == amountA;
            ensures coinB_amount - coinB_amount_post == amountB;

            
        }


        // with certain amount of TokenA, calculate the price after swapping
        public entry fun est_price<TokenA,TokenB>(amountA:u64):u64 acquires Pair{
            let y=calcu_amountB<TokenA,TokenB>(amountA);
            y*AMOUNT_MUTIPLIER/amountA
        }

        public(friend) fun calcl_fee<TokenA:drop,TokenB:drop>(amountA:u64):u64 acquires Pair{
            let pair=borrow_global<Pair<TokenA,TokenB>>(MODULE_OWNER);
            amountA*pair.fee_rate / 10000
        }

        public(friend) fun calcu_amountB<TokenA,TokenB>(amountA:u64):u64 acquires Pair{
            let pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            let k = pair.amountA * pair.amountB;
            let y= pair.amountB;
            let x= pair.amountA;
            y-k/(x+amountA)
        }

        public(friend) fun collect_fee<TokenA,TokenB>(amount:u64) acquires Pair{
            let pair=borrow_global_mut<Pair<TokenA,TokenB>>(MODULE_OWNER);
            pair.fee = pair.fee+amount;
        }

        // debug only
        public fun check_pool<TokenA,TokenB,LPToken>(addr:address) acquires Pair{
            let pair = borrow_global<Pair<TokenA,TokenB>>(addr);
            debug::print(pair);
            debug::print(&BaseCoin::balance_of<LPToken>(addr));
        }

        public fun assert_pool<TokenA,TokenB,LPToken>(addr:address,amountA:u64,amountB:u64,fee:u64,lptoken:u64) acquires Pair{
            let pair = borrow_global<Pair<TokenA,TokenB>>(addr);
            let lp = BaseCoin::balance_of<LPToken>(addr);
            assert!((amountA == pair.amountA),0);
            assert!((amountB == pair.amountB),0);
            assert!((fee == pair.fee),0);
            assert!((lptoken == lp),0);

        }

        
    }

    
// ---------------------------test moduel----------------------
    module test{
            use 0x2::swap_coin;
            use 0x2::pair;
            use std::debug;
            use 0x2::BaseCoin;

            const FEE_RATE_10:u64=10;
            const FEE_RATE_50:u64=50;
            const FEE_RATE_100:u64=100;
            const FEE_RATE_300:u64=300;

            struct SilverCoin has drop{ }
            struct GoldCoin has drop{ }
            struct LPToken has drop{ }

            #[test(_lp1=@0xa,_lp1sg=@0xa,_lp2=@0x4,_lp2sg=@0x4,_taker1=@0x5,_owner=@0x6,_ownersg=@0x6)]
            fun test_funs(_lp1sg:&signer,_lp1:address,_lp2:address,_lp2sg:&signer,_taker1:address,_owner:address,_ownersg:&signer){
                
                BaseCoin::init_balance<GoldCoin>(_lp1sg);
                BaseCoin::init_balance<GoldCoin>(_lp2sg);
                BaseCoin::init_balance<GoldCoin>(_ownersg);

                BaseCoin::init_balance<SilverCoin>(_lp1sg);
                BaseCoin::init_balance<SilverCoin>(_lp2sg);
                BaseCoin::init_balance<SilverCoin>(_ownersg);

                BaseCoin::init_balance<LPToken>(_lp1sg);
                BaseCoin::init_balance<LPToken>(_lp2sg);
                BaseCoin::init_balance<LPToken>(_ownersg);
                
                BaseCoin::mint<GoldCoin>(_lp1,20000);
                BaseCoin::mint<SilverCoin>(_lp1,1000);
                
                BaseCoin::mint<GoldCoin>(_lp2,3000);
                BaseCoin::mint<SilverCoin>(_lp2,100);

                BaseCoin::mint<GoldCoin>(_owner,1000);
                BaseCoin::mint<SilverCoin>(_owner,2000);
                BaseCoin::mint<LPToken>(_owner,500);
                BaseCoin::mint<LPToken>(_lp1,10000);
                BaseCoin::mint<LPToken>(_lp2,10000);

                
                // init pool
                pair::init_pair<GoldCoin,SilverCoin>(_ownersg,FEE_RATE_10);

                debug::print(& 10000);
                pair::init_pair<GoldCoin,LPToken>(_ownersg,FEE_RATE_10);
                pair::init_pair<SilverCoin,LPToken>(_ownersg,FEE_RATE_10);

                pair::add_liquid<GoldCoin,SilverCoin,LPToken>(_lp1sg,10000,1000);
                pair::add_liquid<GoldCoin,SilverCoin,LPToken>(_lp2sg,1000,100);
                pair::add_liquid<GoldCoin,LPToken,LPToken>(_ownersg,100,50);

                debug::print(& 20000);
                
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp1);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp2);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_owner);
                debug::print(& 30000);
                
                swap_coin::swap_coin<GoldCoin,SilverCoin,LPToken>(_lp1sg,1000);
                debug::print(& 40000);
                
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp1);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp2);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_owner);

                pair::remove_liquid<GoldCoin,SilverCoin,LPToken>(_lp1sg,20);

                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp1);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_lp2);
                pair::check_pool<GoldCoin,SilverCoin,LPToken>(_owner);
                // debug::print(& 40000);
                
                
                

            }
    }
    
    

}
