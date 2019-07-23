let fact = function(n, total) {
    return n === 0 ? total : fact(n - 1, total * n);
}

console.log(fact(100000, 1))
