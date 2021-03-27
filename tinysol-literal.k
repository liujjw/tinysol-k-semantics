// Exact tinysol syntax and semantics, not working.

module TINYSOL-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Id ::= "#a(0)_call" [token] | "contract" [token]
    syntax ChainState ::= "balances" Balances ";"
                        | Addr "fun" Id "(" Ids ")" Block
                        | "var" Ids ";"
                        // | "contract" Addr Block 
    syntax Balances ::= List{Balance, ","}
    syntax Balance ::= Addr Int "$" 
    syntax ContractID ::= Addr
    syntax Ids ::= List{Id, ","}

    syntax AExp  ::= Int
                | AExp "*" AExp              [strict, left]
                | AExp "/" AExp              [strict, left] 
                > AExp "+" AExp              [left, strict]
                > AExp "-" AExp              [left, strict]
                | "(" AExp ")"               [bracket]

    syntax BExp  ::= Bool
                | AExp "<=" AExp             [seqstrict]
                | AExp ">=" AExp             [seqstrict]
                | AExp "<" AExp              [seqstrict]
                | AExp ">" AExp              [seqstrict]
                | AExp "==" AExp             [seqstrict]
                | AExp "!=" AExp             [seqstrict]
                | "(" BExp ")"               [bracket]
                | "!" BExp                   [strict]
                > BExp "&&" BExp             [left, strict(1)]
                > BExp "||" BExp             [left, strict(1)]

    // depends on calling context
    syntax Const ::= "^sender" | "^value"

    // non contract addresses are the trivial contract, which must be specified in syntax
    syntax Addr ::= "#a" "(" Int ")" 

    // old 
    // imperative functions  
    // syntax Proc ::= Id "(" FArgs ")" Block 
    // syntax FArgs ::= List{Id, ","}
    // syntax Args ::= List{E, ","}            [strict]
    // syntax Procs ::= List{Proc,","} 
    // syntax BoundContract ::= Addr " has " Procs 
    // syntax AddrBalance ::= Addr " owns " Int 
    // syntax ContractOrBalance ::= BoundContract | AddrBalance 
    // syntax Inits ::= List{ContractOrBalance,";"}
    // init gamma 
    // TODO last contract passed in is initial sending address 
    // syntax Pgm ::= "Call." BoundContract Block 
    // body of program is "off-chain", contracts are on chain 

    syntax Block ::= "{" "}"
                    | "{" S "}"

    syntax S ::= "skip" 
                | ChainState | E ";"                            // addition to formal syntax  
                | "throw" ";"                                   // uncatchable, revert all state updates  
                // > S ";" S
                | "if" "(" BExp ")" "then" Block "else" Block   [strict(1)]
                | "while" "(" BExp ")" "do" Block 
                | E " : " Id "(" Ids ")" " $ " E ";"
                | Block 
                | E ";"                                       [strict]
                | "print" "(" E ")"  ";"                        [strict] // for debugging 

    // easier to use with k rules than S;S
    syntax Ss ::= S | Ss Ss                                     [right]

    // [op E] expression ommitted, used AExp/BExp instead
    syntax E ::= AExp
                | BExp 
                | Const
                | Addr 
                | "?"Id                     // bound value 
                | "!"Id                     // whether bound  
                | Addr" : "E                // E in context of Addr
                | Addr" : " "?balance"
                 > E "=" E             [strict(2), right]

    // desugaring 
    rule balances #a(B)(C:Int)$, #a(D)(E:Int)$, Fs:Balances; => balances #a(B)C$; balances #a(D)E$, Fs;                       [macro-rec]
    rule var X:Id = E; => var X; X = E;             [macro]
endmodule

module TINYSOL
    imports TINYSOL-SYNTAX
    imports DOMAINS

    // lambdas and not closures because functions are in contracts,  
    // which are "global"  
    syntax Val ::= Int | Bool | Id | lambda(Id, S) | "Nil"
    syntax Vals ::= List{Val, ","}
    syntax KResult ::= Val

    // gamma: Addr -> Contract
    // sigma: Addr -> (Val -> Val), roughly the state, the semantics is the state transition function
    // rho: Const -> naturals
    // (abstract state updates) pi: Addr -> (Val -> Val) 
    // no gas in tinysol, so state updates do not revert if insufficient, ie assume always enough gas 
    // addresses are "permanent", ie are not really pointers
    // difficult to capture the exact formalism, so only simulate the semantics 
    syntax ControlCell
    syntax ControlCellFragment
   
    configuration <T>
                  <k> $PGM:S </k>
                  <procedures> .Map </procedures>
                  <sender> 0 </sender>
                  <value> 0 </value>
                  <ledger> .Map </ledger>
                </T>

    // store procedures
    rule <k> #a(_B:Int) fun F(As) S => . ...</k>
        <procedures> ... .Map => L |-> lambda(As, S) ... </procedures>

    // contract storage
    syntax KItem ::= "undefined"  [latex(\bot)]
    rule <k> var X:Id; => . ...</k>
       <state> ... .Map =>  X |-> "undefined" ... </state>

    // store balances  
    rule <k> balances #a(B:Int)(C:Int)$; => . ...</k>
        <ledger> ... .Map => B |-> C ... </ledger>
    // lookup balances
    rule <k> #a(B) : ?balance => C ...</k> 
        <ledger>... B |-> C ...</ledger>  [lookup]

    // function calls
    syntax KItem ::= (Map,K,ControlCellFragment)
    rule <k> lambda(Xs,S)(Vs:Vals) ~> K => mkDecls(Xs,Vs) S; </k>
    syntax S ::= mkDecls(Ids,Vals)  [function]
    rule mkDecls((X:Id, Xs:Ids), (V:Val, Vs:Vals)) => var X=V; mkDecls(Xs,Vs)
    rule mkDecls(.Ids,.Vals) => {}

    // standard imperative features
    rule I1 + I2 => I1 +Int I2
    rule I1 - I2 => I1 -Int I2
    rule I1 * I2 => I1 *Int I2
    rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
    rule I1 <= I2 => I1 <=Int I2    
    rule I1 >= I2 => I1 >=Int I2
    rule I1 < I2 => I1 <Int I2    
    rule I1 > I2 => I1 >Int I2
    rule I1 == I2 => I1 ==Int I2    
    rule I1 != I2 => I1 =/=Int I2
    rule I1 && I2 => I1 andBool I2
    rule ! B1 => notBool B1
    rule skip => .
    rule {} => .   [structural]
    rule {S} => S  [structural]
    rule if (true)  then S else _ => S
    rule if (false) then _ else S => S
    rule true  || _ => true
    rule false || E => E
    // rule S1:S;S2:S => S1 ~> S2  [structural]
    //rule while (B) do S => if (B) {S while (B) do S} else {}  [structural]

    // TODO undefined semantics result in all state updates being reverted 

    // attempt at exact formalism in k:
    // rule <k> X:Const => Y ...</k><rho> ... X |-> Y ... </rho>
    // rule <k> I:Id</k><sigma>... Map[A] ... </sigma><contract> A </contract>
    // addresses cannot update their balances syntactically, only the semantics can 
    // lookup   
    // rule <k> ?X:Addr => C ...</k><env>... X |-> C ...</env>
    // rule <k> ?X:Addr => S ...</k><store>... X |-> S ...</store>
    // assignment for sigma, no assigment for env (no contract creation)
    // rule <k> X:Addr := ; => . ...</k> <store>... X |-> (_ => I) ...</store>
    // todo add value for balance key
    // global declaration (initialization) 
    //rule <k> (X,Xs => Xs); ...</k>
         //<env> Rho => Rho[X <- !N:Contract] </env>
         //<store>... .Map => !N |-> 0 ...</store>
    // create map from addresses to contracts 
    // rule <k>A:Addr -> C:Contract : _ => . ... </k><gamma> A |-> C </gamma>
    // initialize sigma with balances 
    //rule <k>_ -> C:Contract : D:Int => . ... </k><sigma> A |-> (balance |-> D) </sigma>

endmodule
