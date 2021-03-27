LEDGER #a(1)10000$, #a(0)5$, #a(2)0$;

contract Wallet {
    var spenderAddress;
    
    fn Wallet(spender) {
        spenderAddress = spender;    
    }

    fn transfer(units, to) {
        if (^sender == spenderAddress && ^value == 1) {
            log("Sending ", units, " to account with initial balance ", BALANCE(to), "\n");
            TRANSFER(units, to);
            log("Balance of account after transfer: ", BALANCE(to), "\n");
        } else {
            log("Cannot spend from this address or need to pay for service.\n");
        }
    }
}

DEPLOY(Wallet(#a(0)), #a(1));

tx {
    from_addr: #a(0),
    to_addr: #a(1),
    value: 1,
    call: {
        name: transfer,
        args: [
            150, 
            #a(2)
        ]
    }
}

tx {
    from_addr: #a(2),
    to_addr: #a(1),
    value: 0,
    call: {
        name: transfer,
        args: [
            5, 
            #a(2)
        ]
    }
}

tx {
    from_addr: #a(0),
    to_addr: #a(1),
    value: 0,
    call: {
        name: transfer,
        args: [
            5, 
            #a(2)
        ]
    }
}