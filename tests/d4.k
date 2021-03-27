LEDGER #a(1)10$, #a(0)10$, #a(2)10$, #a(3)10$, #a(4)10$;

contract C {
    fn C() {skip;}

    fn f(a, b, d) {
        if (b) {
            CONTRACT(d).g();
            TRANSFER(^value, a);
        }
    }
}

contract D {
    fn D() {skip;}

    fn g() {
        CONTRACT(^sender).f(#a(4), false, ADDRESS(this));
    }
}

DEPLOY(C(), #a(1));
DEPLOY(D(), #a(2));

tx {
    from_addr: #a(0),
    to_addr: #a(1),
    value: 10,
    call: {
        name: f,
        args: [
            #a(3),
            true, 
            #a(2)
        ]
    }
}