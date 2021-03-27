// Global functions only

module TINYSOL-SYNTAX
    imports DOMAINS-SYNTAX
    syntax Id ::= "call" [token]

    syntax Decl ::= "var" Exps ";"
                | "balances" Balances ";"
                | "contract" Addr "{" ContractBlock "}"

    syntax Proc ::= "fn" Id "(" Ids ")" Block

    syntax ContractBlock ::= Proc 
                            | ContractBlock ContractBlock       [right]

    syntax Balances ::= List{Balance, ","}
    syntax Balance ::= Addr Int "$"
    syntax Const ::= "^sender" | "^value"
    syntax Addr ::= "#a" "(" Int ")"
    syntax Exp ::= Int | Bool | String | Id 
                | Const
                | Addr 
                | "?"Id                     
                | "!"Id                     
                | Addr":"Id                
                | Addr":?balance"
                | "(" Exp ")"             [bracket]
                > Exp "(" Exps ")"        [strict]
                | "-" Exp                 [strict]
                | "read" "(" ")"
                > left:
                    Exp "*" Exp           [strict, left]
                | Exp "/" Exp             [strict, left]
                | Exp "%" Exp             [strict, left]
                > left:
                    Exp "+" Exp           [strict, left]
                | Exp "-" Exp             [strict, left]
                > non-assoc:    
                    Exp "<" Exp           [strict, non-assoc]
                | Exp "<=" Exp            [strict, non-assoc]
                | Exp ">" Exp             [strict, non-assoc]
                | Exp ">=" Exp            [strict, non-assoc]
                | Exp "==" Exp            [strict, non-assoc]
                | Exp "!=" Exp            [strict, non-assoc]
                > "!" Exp                 [strict]
                > left:
                Exp "&&" Exp              [strict(1), left]
                | Exp "||" Exp            [strict(1), left]
                > Exp "=" Exp             [strict(2), right]

    syntax Ids  ::= List{Id,","}
    syntax Exps ::= List{Exp,","}          [strict]  
    //syntax Exps ::= Ids
    syntax Val
    syntax Vals ::= List{Val,","}
    syntax Bottom
    syntax Bottoms ::= List{Bottom,","}
    syntax Ids ::= Bottoms

    
    syntax Block ::= "{" "}"
                | "{" Stmts "}"

    syntax Stmt ::= Decl | Block | Proc
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "throw" ";"                           [strict]
                | "skip" ";"
                | Exp "$" Exp ";"                       [strict, non-assoc]

    syntax Stmts ::= Stmt
                | Stmts Stmts                           [right]

    rule if (E) S => if (E) S else {}    
    rule var X:Id = E; => var X; X = E;                              [macro]
    rule balances #a(B)(C:Int)$, #a(D)(E:Int)$, Fs:Balances; => balances #a(B)C$; balances #a(D)E$, Fs;                                        [macro-rec]
    

endmodule


module TINYSOL
    imports TINYSOL-SYNTAX
    imports DOMAINS

    syntax Val ::= Int | Bool | String
               | lambda(Ids,Stmt) | Addr 

    syntax Exp ::= Val
    syntax Exps ::= Vals
    syntax Vals ::= Bottoms
    syntax KResult ::= Val
                    | Vals 

    syntax ControlCell
    syntax ControlCellFragment

    configuration 
                <k> $PGM:Stmts ~> execute </k>
                <control>
                    <fstack> .List </fstack>
                </control>
                <env> .Map </env>
                <genv> .Map </genv>
                <store> .Map </store>
                <output stream="stdout"> .List </output>
                <nextLoc> 0 </nextLoc>
                <ledger> .Map </ledger>
                <initLedger> .Map </initLedger>
                <senderID> 0 </senderID>
                <value> 0 </value>

    rule <k> skip; => . ... </k>

    rule <k> contract (_A:Addr) { C } => C ... </k>
    
    rule <k> ^sender => #a(S) ... </k>
        <senderID> S </senderID>

    rule <k> ^value => V ... </k>
        <value> V </value>

    rule <k> throw; => . ... </k>
        <ledger> _ => Il </ledger>
        <senderID> _ => 0 </senderID>
        <value> _ => 0 </value>
        <initLedger> Il </initLedger>

    syntax KItem ::= "check(" Int "," Int "," Int "," Int ")"
    syntax KItem ::= "update(" Int "," Int "," Int "," Int ")"
    rule <k> (I:Int)$#a(B:Int); => . ~> check(I,S,B,C) ... </k>
        <value> _ => I </value>
        <senderID> S </senderID>
        <ledger> ... B |-> C ... </ledger>   

    rule <k> check(I,S,B,C) => update(I,S,B,C) ... </k>
        <ledger> ... S |-> D ... </ledger> requires D >=Int I 

    syntax KItem ::= "update2(" Int "," Int ")"
    rule <k> update(I,S,B,C) => update2(I,S) ... </k>
        <ledger> Ledger => Ledger[B <- I +Int C] </ledger>

    syntax KItem ::= "update3(" Int "," Int "," Int ")"
    rule <k> update2(I,S) => update3(I,S,C) ... </k>
        <ledger> ... S |-> C ... </ledger>
    
    rule <k> update3(I,S,C) => . ... </k>
        <ledger> Ledger => Ledger[S <- C -Int I] </ledger>

    rule <k> balances #a(B:Int)(C:Int)$; => . ...</k>
        <ledger> ... .Map => B |-> C ... </ledger>
        <initLedger> ... .Map => B |-> C ... </initLedger>

    rule <k> #a(B):?balance => C ...</k> 
        <ledger>... B |-> C ...</ledger>                [lookup]

    syntax KItem ::= "undefined"  
    rule <k> var X:Id; => . ...</k>
        <env> Env => Env[X <- L] </env>
        <store>... .Map => L |-> undefined ...</store>
        <nextLoc> L => L +Int 1 </nextLoc>

    rule <k> fn F(Xs) S => . ...</k>
        <env> Env => Env[F <- L] </env>
        <store>... .Map => L |-> lambda(Xs, S) ...</store>
        <nextLoc> L => L +Int 1 </nextLoc>

    syntax KItem ::= "execute"
    rule <k> execute => call(.Exps); </k>
        <env> Env </env>
        <genv> .Map => Env </genv>  [structural]

    rule <k> X:Id => V ...</k>
        <env>... X |-> L ...</env>
        <store>... L |-> V:Val ...</store>  [lookup]

    rule I1 + I2 => I1 +Int I2
    rule Str1 + Str2 => Str1 +String Str2
    rule I1 - I2 => I1 -Int I2
    rule I1 * I2 => I1 *Int I2
    rule I1 / I2 => I1 /Int I2 requires I2 =/=K 0
    rule I1 % I2 => I1 %Int I2 requires I2 =/=K 0
    rule - I => 0 -Int I
    rule I1 < I2 => I1 <Int I2
    rule I1 <= I2 => I1 <=Int I2
    rule I1 > I2 => I1 >Int I2
    rule I1 >= I2 => I1 >=Int I2

    rule V1:Val == V2:Val => V1 ==K V2
    rule V1:Val != V2:Val => V1 =/=K V2

    rule ! T => notBool(T)
    rule true  && E => E
    rule false && _ => false
    rule true  || _ => true
    rule false || E => E

    syntax KItem ::=  (Map,K,ControlCellFragment)

    rule <k> lambda(Xs,S)(Vs:Vals) ~> K => mkDecls(Xs,Vs) S return; </k>
        <control>
            <fstack> .List => ListItem((Env,K,C)) ...</fstack>
            C
        </control>
        <env> Env => GEnv </env>
        <genv> GEnv </genv>

    rule <k> return(V:Val); ~> _ => V ~> K </k>
        <control>
            <fstack> ListItem((Env,K,C)) => .List ...</fstack>
            (_ => C)
        </control>
        <env> _ => Env </env>

    syntax Val ::= "nothing"
    rule return; => return nothing;   [macro]

    context (HOLE => lvalue(HOLE)) = _
    rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (_ => V) ...</store>
    [assignment]

    rule {} => .  [structural]
    rule <k> { S } => S ~> setEnv(Env) ...</k>  <env> Env </env>  [structural]

    rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]
    rule C1:ContractBlock C2:ContractBlock => C1 ~> C2  [structural]

    rule _:Val; => .

    rule if ( true) S else _ => S
    rule if (false) _ else S => S

    rule while (E) S => if (E) {S while(E)S} else {} [structural]

    rule <k> print(V:Val, Es => Es); ...</k> <output>... .List => ListItem(V) </output> [print]
    rule print(.Vals); => .  [structural]

    syntax Stmts ::= mkDecls(Ids,Vals)  [fn]
    rule mkDecls((X:Id, Xs:Ids), (V:Val, Vs:Vals)) => var X=V; mkDecls(Xs,Vs)
    rule mkDecls(.Ids,.Vals) => {}

    syntax Exp ::= lookup(Int)
    rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

    syntax KItem ::= setEnv(Map)
    rule <k> setEnv(Env) => . ...</k> <env> _ => Env </env>  [structural]

    rule (setEnv(_) => .) ~> setEnv(_)  [structural]

    syntax Exp ::= lvalue(K)
    syntax Val ::= loc(Int)

    rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

    rule lvalue(lookup(L:Int) => loc(L))  [structural]

endmodule

/*
    syntax KItem ::= Int "$$" Addr ";" Int "-$" Addr ";"
    rule <k> (I:Int)$#a(B:Int); => (I +Int C)$$#a(B);I-$#a(S); ... </k>
        <value> _ => I </value>
        <sender> S </sender>
        <ledger> ... B |-> C ... </ledger>              

    syntax KItem ::= Int "-$" Addr ";"
    rule <k> (I:Int)$$#a(B);I-$#a(S); => I-$#a(S); ... </k>
        <ledger> Ledger => Ledger[B <- I] </ledger>     
    
    syntax KItem ::= Int "-$$" Addr ";"
    rule <k> (I:Int)-$#a(B:Int); => (C -Int I)-$$#a(B); ... </k>
        <ledger> ... B |-> C ... </ledger>              

    rule <k> (I:Int)-$$#a(B:Int); => . ... </k>
        <ledger> Ledger => Ledger[B <- I] </ledger>


    rule <k> I:Id(E1:Exps)->(E2)$(A:Addr); => E2$A; I(E1) ... </k>


    | Id "(" Exps ")" "->" Int "$" Addr ";"
*/