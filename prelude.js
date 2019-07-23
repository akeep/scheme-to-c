function trampoline(thunk) {
    while (thunk && typeof thunk === "function") {
        thunk = thunk();
    }
    return thunk
}

function add(a, b) {
    return a + b;
}

function times(a, b) {
    return a * b;
}

let program =
