proc; simul//=.*.
simul //=.
auto*.
by auto* ; case -> .
by apply/(allP _)/andp_right <- + allNpred/.
by move=> i [? ?]; exists x.+1.
by do! step.
do!step.
case: {IH}(#|predT|/ #|predT| \\in enum 'I_(size l))=> [[l'] | ] _.
call/=.
by call/.; rewrite /Runn' /= !ifE //= eqxx andbC ifN//=> -> *.
have:= gePP P^2 ((Pr[_@&m:`true]/#|predT|)%Reals)^2 .
case: {IH}(#|predT|/ #|predT| \\in enum 'I_(size l))=> [[l'] | ] _.
have := sqrtsubneg A B by [] .
by [apply sqrtA | auto with zarith RealArith].
by have := sqrtsubneg A B where '['a']:=hge1 and '['b']:=@leqZZl S T U V W X Y Z AA BB CC DD EE FF GG HH II JJ KK LL MM NN OO PP RR SS TT UU XX YY ZZ. (* Here the parse error was: illegal use of character: ' *)
have := sqrtsubneg A B by [] .
congr (\\big[+%R/(Pr[IRunner(I, F, FRO).run() @ &m : success res.`1]))_(arg | true)).
rewrite {}/pr_runner_succ; apply leq_trans with.
have -> := (@bigID _ [predC iotaQ]).
have->:=@bigid _.
by congr (_ + \\big[_/_]_)_^_.
congr (\\big[+%R/(Pr[IRunner(I, F, FRO).run() @ &m : success res.`1]))_(arg | true)).
apply/(@bigID['a])=> //.
by rewrite.
by.
rewrite /.
apply(*
have=>(/((*
by*)