LEDGER #a(1)1000$, #a(0)5$, #a(2)0$;

contract Seller {
    var skins;
    var buyerAddress;
    var buyerTokens;

    fn Seller(x, y, z) {
        skins = x;
        buyerAddress = y;
        buyerTokens = z;
    }

    fn buy(receiverAddress) {
        if (skins > 0 && buyerTokens >= 10 && ^sender == buyerAddress) {
            send();
            CONTRACT(receiverAddress).deliver();
            buyerTokens = buyerTokens - 10;
        }
    }

    fn logSkins() {
        log("Number of skins remaining now: ", skins, "\n");
    }

    fn send() {
        skins = skins - 1;
    }
}

contract Receiver {
    fn Receiver() { skip; }

    fn deliver() {
        CONTRACT(^sender).buy(ADDRESS(this));
    }

    fn start(sellerAddr) {
        log("Starting re-entrant calls. \n");
        CONTRACT(sellerAddr).buy(ADDRESS(this));
    }
}

DEPLOY(Seller(5, #a(2), 10), #a(1));
DEPLOY(Receiver(), #a(2));

tx {
    from_addr: #a(0),
    to_addr: #a(1),
    value: 0,
    call: {
        name: logSkins,
        args: []
    }
}

tx {
    from_addr: #a(0),
    to_addr: #a(2),
    value: 0,
    call: {
        name: start,
        args: [
            #a(1)
        ]
    }
}

tx {
    from_addr: #a(0),
    to_addr: #a(1),
    value: 0,
    call: {
        name: logSkins,
        args: []
    }
}
