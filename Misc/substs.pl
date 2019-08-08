substitute(empty,_,_,empty).

substitute(top,_,_,top).
substitute(unit,_,_,unit).

substitute(bool,_,_,bool).
substitute(on,_,_,on).
substitute(off,_,_,off).

substitute(nat,_,_,nat).
substitute(zero,_,_,zero).
substitute(suc(X),Var,For,suc(SubX)) :- substitute(X,Var,For,SubX).

substitute(list(T),Var,For,list(SubT)) :- substitute(T,Var,For,SubT).
substitute(emptyList,_,_,emptyList).
substitute(concat(X,Xs),Var,For,concat(SubX,SubXs)) :- substitute(X,Var,For,SubX), substitute(Xs,Var,For,SubXs).

substitute(variable(X),variable(X),For,For).
substitute(variable(X),variable(Y),_,variable(X)) :- X \= Y.


