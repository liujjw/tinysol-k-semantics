//-----------------------------------------------------------------------
// K definitions for TinySol, a subset of Solidity. 
//
// Based on the KOOL Object Oriented language in the K-framework 
// tutorials: https://kframework.org/k-distribution/tutorial/
//
// Jackie Liu, jl2627
//-----------------------------------------------------------------------

module TINYSOL-OO-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Id ::= "Offchain" [token] | "Base" [token]  

    syntax Decl ::= "var" Exps ";"
                | "contract" Id Block 
                | "fn" Id "(" Ids ")" Block

    syntax Balances ::= List{Balance, ","}
    syntax Balance ::= Addr Int "$"
    syntax Const ::= "^sender" | "^value"
    syntax Addr ::= "#a" "(" Int ")"
    syntax Exp ::= Int | Bool | String | Id 
                | Const
                | Addr
                | Exp "." Id         
                | "this"            
                | "BALANCE(" Exp ")"      [strict]
                | "DEPLOY(" Id "(" Exps ")" "," Addr ")" [strict(2)]
                | "CONTRACT(" Exp ")"     [strict]
                | "ADDRESS(" Exp ")"      [strict]
                | "(" Exp ")"             [bracket]
                > Exp "(" Exps ")"        [strict(2)]
                | "-" Exp                 [strict]
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
    syntax Exps ::= List{Exp,","}         [strict, klabel(exps)]  
    syntax Val
    syntax Vals ::= List{Val,","}         [klabel(exps)]

    syntax Block ::= "{" "}"
                | "{" Stmts "}"

    syntax Stmt ::= Decl | Block 
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "log" "(" Exps ")" ";"                [strict]
                | "throw" ";"                           [strict]
                | "skip" ";"
                | "TRANSFER(" Exp "," Exp ")" ";"       [strict]
                | "LEDGER" Balances ";" 
                | "tx" Addr "{" Stmts "}"
                | "tx" "{" TxFieldLst "}"

    syntax TxFieldLst ::= "from_addr" ":" Addr "," "to_addr" ":" Addr "," "value" ":" Int "," "call" ":" "{" CallLst "}"

    syntax CallLst ::= "name" ":" Id "," "args" ":" "[" Exps "]"

    syntax Stmts ::= Stmt
                | Stmts Stmts                           [right]

    rule if (E) S => if (E) S else {}    
    rule var X:Id = E; => var X; X = E;                              [macro]
    rule LEDGER #a(B)(C:Int)$, #a(D)(E:Int)$, Fs:Balances; => LEDGER #a(B)C$; LEDGER #a(D)E$, Fs;                                        [macro-rec]
    

endmodule


module TINYSOL-OO
    imports TINYSOL-OO-SYNTAX
    imports DOMAINS

    syntax Val ::= Int | Bool | String | Addr 

    syntax Exp ::= Val
    syntax Exps ::= Vals
    syntax KResult ::= Val
                    | Vals 

    syntax EnvCell
    syntax ControlCell
    syntax EnvStackCell
    syntax CrntObjCellFragment

    // make value stacked and remove holder
    configuration <T>
                <k> $PGM:Stmts </k>

                <control>
                    <fstack> .List </fstack>
                    <crntObj>  
                           <crntContract> Offchain </crntContract>
                           <envStack> .List </envStack>
                           <addressID> -1 </addressID>
                           <senderID> -1 </senderID>
                           <location multiplicity="?"> .K </location>
                    </crntObj>
                </control>

                <contracts>     
                     <contractData multiplicity="*" type="Map">
                        <contractName> Offchain </contractName>
                        <baseContract> Base </baseContract>
                        <declarations> .K </declarations>
                     </contractData>
                </contracts>

                <env> .Map </env>
                <genv> .Map </genv>
                <store> .Map </store>
                <output stream="stdout"> .List </output>
                <nextLoc> 0 </nextLoc>

                <gamma> .Map </gamma>
                <ledger> .Map </ledger>
                <initLedger> .Map </initLedger>
                <value> 0 </value>      
                <holder> -1 </holder>
    </T>   
    
    rule <k> skip; => . ... </k>

    // contract addresses cannot initiate transactions
    rule <k> tx #a(I:Int) { C } => C ... </k>
        <crntObj> <crntContract> CC => CC </crntContract> <envStack> ES => ES </envStack> <addressID> _ => I </addressID> <senderID> S => S </senderID> </crntObj>
    
    rule <k> ^sender => #a(S) ... </k>
        <crntObj> <crntContract> _CC </crntContract> <envStack> _ES </envStack> <addressID> _I </addressID> <senderID> S </senderID> </crntObj>

    rule <k> ^value => V ... </k>
        <value> V </value>

    // revert the state and go back to offchain object
    rule <k> throw; => log("Error. Balances reverted. "); </k>
        <ledger> _ => Il </ledger>
        <value> _ => 0 </value>
        <initLedger> Il </initLedger>

    rule <k> tx {from_addr: A, to_addr: B, value: V, call: {name: F, args: [Xs]}} => tx A {TRANSFER(V, B);CONTRACT(B).F(Xs);} ...</k> requires V =/=Int 0
    
    rule <k> tx {from_addr: A, to_addr: B, value: V, call: {name: F, args: [Xs]}} => tx A {CONTRACT(B).F(Xs);} ...</k> requires V ==Int 0

    syntax KItem ::= "check(" Int "," Int "," Int "," Int ")"
    syntax KItem ::= "update(" Int "," Int "," Int "," Int ")"
    rule <k> TRANSFER(I:Int, #a(B:Int)); => check(I,S,B,C) ... </k>
        <value> _ => I </value>
        <crntObj> <crntContract> _CC </crntContract> <envStack> _ES </envStack> <addressID> S </addressID> <senderID> _Ss </senderID> </crntObj>
        <ledger> ... B |-> C ... </ledger>   

    // log an insufficient balance message 
    rule <k> check(I:Int,S:Int,B:Int,C:Int) => update(I,S,B,C) ... </k>
        <ledger> ... S |-> D ... </ledger> requires D >=Int I 

    syntax KItem ::= "update2(" Int "," Int ")"
    rule <k> update(I,S,B,C) => update2(I,S) ... </k>
        <ledger> Ledger => Ledger[B <- I +Int C] </ledger>

    syntax KItem ::= "update3(" Int "," Int "," Int ")"
    rule <k> update2(I,S) => update3(I,S,C) ... </k>
        <ledger> ... S |-> C ... </ledger>
    
    rule <k> update3(I,S,C) => . ... </k>
        <ledger> Ledger => Ledger[S <- C -Int I] </ledger>

    rule <k> LEDGER #a(B:Int)(C:Int)$; => . ...</k>
        <ledger> ... .Map => B |-> C ... </ledger>
        <initLedger> ... .Map => B |-> C ... </initLedger>

    rule <k> BALANCE(#a(B)) => C ...</k> 
        <ledger>... B |-> C ...</ledger>                [lookup]

    syntax KItem ::= "undefined"  
    rule <k> var X:Id; => . ...</k>
        <env> Env => Env[X <- L] </env>
        <store>... .Map => L |-> undefined ...</store>
        <nextLoc> L => L +Int 1 </nextLoc>

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

    syntax Exp ::= lookupMember(List, Id)  [function]

    rule lookupMember(ListItem(envStackFrame(_, X|->L _)) _, X)
    => lookup(L)

    rule lookupMember(ListItem(envStackFrame(_, Env)) Rest, X) =>
       lookupMember(Rest, X)
    when notBool(X in keys(Env))

    rule <k> lvalue(X:Id => this . X) ...</k>  <env> Env </env>
    when notBool(X in keys(Env))  [structural]

    context lvalue((HOLE . _)::Exp)

    rule lvalue(objectClosure(_Sender, _Address, Contract, ListItem(envStackFrame(Contract,Env)) EStack)
              . X
              => lookupMember(ListItem(envStackFrame(Contract,Env)) EStack,
                              X))  [structural]
    rule lvalue(objectClosure(_Sender, _Address, Contract, (ListItem(envStackFrame(Contract':Id,_)) => .List) _)
              . X)
    when Contract =/=K Contract'  [structural]

    rule <k> (lookup(L) => V)(_:Exps) ...</k>  <store>... L |-> V:Val ...</store> [lookup]

    rule <k> (X:Id => V)(_:Exps) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

    rule <k> (X:Id => this . X)(_:Exps) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [structural]

    context HOLE._::Id(_) 

    rule (objectClosure(_, _, _, EStack) . X
    => lookupMember(EStack, X:Id))(_:Exps)  [structural]

    rule (A:Exp(B:Exps))(C:Exps) => A(B) ~> #freezerFunCall(C)
    rule V:Val ~> #freezerFunCall(C:Exps) => V(C)
    syntax KItem ::= "#freezerFunCall" "(" K ")"

    rule <k> X:Id => this . X ...</k> <env> Env:Map </env>
    when notBool(X in keys(Env))  [structural]

    context HOLE._::Id 

    rule objectClosure(_, _, Contract:Id, ListItem(envStackFrame(Contract,Env)) EStack)
        . X:Id
    => lookupMember(ListItem(envStackFrame(Contract,Env)) EStack, X)
    [structural]

    rule objectClosure(_, _, Contract:Id, (ListItem(envStackFrame(Contract':Id,_)) => .List) _)
        . X:Id
    when Contract =/=K Contract'  [structural]

    rule <k> this => objectClosure(S, I, CC, ES) ...</k>
       <crntObj> <crntContract> CC </crntContract> <envStack> ES </envStack> <addressID> I </addressID> <senderID> S </senderID> </crntObj>

    rule <k> ADDRESS(objectClosure(_, I, _, _)) => #a(I) ... </k>

    syntax KItem ::= "storeObj"

    rule <k> storeObj => . ...</k>
       <crntObj> <crntContract> CC </crntContract> <addressID> I </addressID> <senderID> S </senderID> <envStack> ES </envStack> (<location> L:Int </location> => .Bag) </crntObj>
       <store>... .Map => L |-> objectClosure(S, I, CC, ES) ...</store>
       <gamma>... .Map => I |-> L ...</gamma>

    rule <k> CONTRACT(#a(I)) => objectClosure(S, A, CC, ES) ... </k>
    <store>... L |-> objectClosure(S, A, CC, ES) ...</store>
    <gamma>... I |-> L ... </gamma>

    syntax KItem ::= "addEnvLayer"

    rule <k> addEnvLayer => . ...</k>
       <env> Env => .Map </env>
       <crntContract> Contract:Id </crntContract>
       <envStack> .List => ListItem(envStackFrame(Contract, Env)) ...</envStack>
    [structural]

    syntax KItem ::= setCrntContract(Id)

    rule <k> setCrntContract(C) => . ...</k>
       <crntContract> _ => C </crntContract>  [structural]

    syntax KItem ::= create(Id)

    rule <k> create(Contract:Id)
           => create(C1) ~> setCrntContract(Contract) ~> S ~> addEnvLayer ...</k>
       <contractName> Contract </contractName>
       <baseContract> C1:Id </baseContract>
       <declarations> S </declarations>  [structural]

    rule <k> create(Base) => . ...</k>  [structural]

    syntax KItem ::= "envStackFrame" "(" Id "," Map ")"

    rule <k> DEPLOY(Contract:Id(Vs:Vals), #a(I:Int)) ~> K
           => create(Contract) ~> storeObj ~> Contract(Vs); return this; </k>
       <env> Env => .Map </env>
       <nextLoc> L:Int => L +Int 1 </nextLoc>
       <control> 
         <crntObj> Obj
                   => <crntContract> Base </crntContract>
                      <envStack> ListItem(envStackFrame(Base, .Map)) </envStack>
                      <location> L </location>
                      <senderID> -1 </senderID>
                      <addressID> I </addressID>
         </crntObj>
         <fstack> .List => ListItem(fstackFrame(Env, K, <crntObj> Obj </crntObj>)) ...</fstack>
       </control>

    rule <k> contract C1 { S } => . ...</k>
       <contracts>... (.Bag => <contractData>
                            <contractName> C1 </contractName>
                            <baseContract> Base </baseContract>
                            <declarations> S </declarations>
                        </contractData>)
       ...</contracts>  [structural]

     rule <k> fn F:Id(Xs:Ids) S => . ...</k>
       <crntContract> Contract:Id </crntContract>
       <location> OL:Int </location>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> methodClosure(Contract,OL,Xs,S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

    syntax Val ::= objectClosure(Int, Int, Id, List)
               | methodClosure(Id,Int,Ids,Stmt)
    syntax KItem ::= fstackFrame(Map,K,K)
                 | (Map,K,K)

    syntax KItem ::= "tempAddr"
    rule <k> tempAddr => . ... </k>
    <holder> _ => A </holder>
    <addressID> A </addressID>

    rule <k> methodClosure(Contract,OL,Xs,S)(Vs:Vals) ~> K
           => mkDecls(Xs,Vs) S return; </k>
       <env> Env => .Map </env>
       <store>... OL |-> objectClosure(_Os, I, _, EnvStack)...</store>
       <control>
          <fstack> .List => ListItem(fstackFrame(Env, K, <crntObj><crntContract> C </crntContract> <envStack> Es </envStack> <addressID> A </addressID> <senderID> Si </senderID> </crntObj>))
          ...</fstack>
          <crntObj> <crntContract> C => Contract </crntContract> <envStack> Es => EnvStack </envStack> <addressID> A => I </addressID> <senderID> Si => A </senderID> </crntObj>
       </control>

    rule <k> return(V:Val); ~> _ => V ~> K </k>
        <control>
            <fstack> ListItem(fstackFrame(Env,K,<crntObj> CI </crntObj>)) => .List ...</fstack>
            <crntObj> _ => CI </crntObj>
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

    rule _:Val; => .

    rule if ( true) S else _ => S
    rule if (false) _ else S => S

    rule while (E) S => if (E) {S while(E)S} [structural]

    // logging a variable referencing an address does not work
    rule <k> log(V:Val, Es => Es); ...</k> <output>... .List => ListItem(V) </output> [log]
    rule log(.Vals); => .  [structural]

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