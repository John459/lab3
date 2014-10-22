1.

    a:
        var x = 5;        
        function f(x) {        
            return function() {            
                return x + 2;                
            };            
        }
        var foo = f(2);
        //bar is 7 in dynamic scoping, and 4 in lexical scoping.        
        var bar = foo();
        
2.

    c:
        Assuming the grammar is not ambiguous, the evaluation order is deterministic because an unambiguous grammar
        generates a unique parse tree.
        
3.

    e1 is evaluated first, followed be e2. This is known because e1 evaluates v1 is written first.
    To change it around, write the evaluation of e2 before writing the evaluation of e1.
    
4.

    a: 
        
        if (obj != null && obj.val > 0) {
            //do stuff
        }
        This is useful because if obj is null then the expression will short-circuit and return false before
        checking the second condition. If this did not happen, then a null-pointer exception would be thrown whenever
        obj was null and this example would not work.
        
    b:
    
        Yes. In e1 && e2, e1 gets evaluated first to v1. If v1 is false, then v1 is returned. e2 is never looked at in
        that case.
