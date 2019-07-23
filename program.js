function trampoline(thunk) {
    while (thunk && typeof thunk === "function") {
//        console.log('boing');
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
(function( k ) { return  (function( k ) { return  k ( (function( kk, fact_0 ) { return  (function(  ) { return  (function( k ) { return  (function( k ) { return  k ( (function( kk, t_3 ) { return  (function(  ) { return  (function( k ) { return  fact_0 ( (function( returnx ) { return  returnx ;}) ) ( k, (function( k ) { return  k ( 5000 ) ;}), (function( k ) { return  k ( 1 ) ;}) ) ;}) ( kk ) ;}) ;}) ) ;}) ( (function( returnx ) { return  returnx ;}) ) ( k, fact_0 = (function( k ) { return  k ( (function( kk, n_1, total_2 ) { return  (function(  ) { return  (function( k ) { return  (function( k ) { return  k ( n_1 ( (function( returnx ) { return  returnx ;}) ) === (function( k ) { return  k ( 0 ) ;}) ( (function( returnx ) { return  returnx ;}) ) ) ;}) ( (function( kif ) { return  /* if */ kif ? (function(  ) { return  total_2 ( k ) ;}) : (function(  ) { return  (function( k ) { return  fact_0 ( (function( returnx ) { return  returnx ;}) ) ( k, (function( k ) { return  k ( add ( n_1 ( (function( returnx ) { return  returnx ;}) ), (function( k ) { return  k ( -1 ) ;}) ( (function( returnx ) { return  returnx ;}) ) ) ) ;}), (function( k ) { return  k ( times ( total_2 ( (function( returnx ) { return  returnx ;}) ), n_1 ( (function( returnx ) { return  returnx ;}) ) ) ) ;}) ) ;}) ( k ) ;}) ;}) ) ;}) ( kk ) ;}) ;}) ) ;}) ) ;}) ( kk ) ;}) ;}) ) ;}) ( (function( returnx ) { return  returnx ;}) ) ( k, (function( k ) { return  k ( undefined ) ;}) ) ;})
;


trampoline(function() {return program (console.log);});
