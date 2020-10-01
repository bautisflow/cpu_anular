% 9. Definir un predicado entr (X,Z,Y) que sea cierto sí y solo sí Z es un entero que pertenece
% al intervalo [X,Y]. Se asume que X e Y siempre van a estar instanciados con números enteros.

%entre(+,+,?)
entre(X,Y,X) :- % Caso base
    X =< Y.
entre(X,Y,Z) :- % Caso recursivo
    X1 is X + 1,
    X1 =< Y,
    entre(X1,Y,Z).

% 12. Escribir  un predicado suma_arrays(A1,A2,A3) que, dados dos términos de la forma array(x1,x2,...,xn),
% A1 y A2, compute un término array(y1,y2,y3) en A3 con la suma de cada uno de los elementos de A1 y A2.

suma_arrays(A1,A2,A3) :-
   functor(A1,array,N),
   functor(A2,array,N),
   functor(A3,array,N),
   add_elements(I,A1,A2,A3).

%%% while I > 0
add_elements(0,_A1,_A2,_A3). % Caso base
add_elements(I,A1,A2,A3) :- % Caso recursivo
    I > 0, % Se podría poner un corte en el predicado anterior como sustitución
    arg(I,A1,X1),
    arg(I,A2,X2),
    X3 is X1 + X2,
    arg(I,A3,X3),
    I1 is I - 1,
    add_elements(I1,A1,A2,A3).
