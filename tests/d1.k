LEDGER #a(1)10$, #a(0)10$, #a(2)10$, #a(3)10$;

contract A {
    var v;

    fn A() {
        v = "zero";
    }

    fn set(newV) {
        log("Setting to ", newV, "\n");
        v = newV;
    }

    fn get() {
        log("Returning ", v, "\n");
        return v;
    }
}

DEPLOY(A(), #a(3));

tx {
    from_addr: #a(0),
    to_addr: #a(3),
    value: 0,
    call: {
        name: set,
        args: [
            "one "
        ]
    }
}

tx {
    from_addr: #a(0),
    to_addr: #a(3),
    value: 0,
    call: {
        name: get,
        args: []
    }
}

tx {
    from_addr: #a(1),
    to_addr: #a(3),
    value: 0,
    call: {
        name: set,
        args: [
            "two "
        ]
    }
}

tx {
    from_addr: #a(1),
    to_addr: #a(3),
    value: 0,
    call: {
        name: get,
        args: []
    }
}

tx {
    from_addr: #a(2),
    to_addr: #a(3),
    value: 0,
    call: {
        name: set,
        args: [
            "three "
        ]
    }
}

tx {
    from_addr: #a(2),
    to_addr: #a(3),
    value: 0,
    call: {
        name: get,
        args: []
    }
}

