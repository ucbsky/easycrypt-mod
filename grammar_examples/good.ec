 proof.
    have /= H0 := Ad1.pr_abs Addh0 a1_ll _ &m (fun b _ => b).
    + by proc;call A_ll;rnd;skip;rewrite /= dt_ll.
    have /= H1 := Ad1.pr_abs Addh1 a1_ll _ &m (fun b _ => b).
    + by proc;call A_ll;do !rnd;skip;rewrite /= dt_ll.
    have -> : 2%r / order%r = inv order%r + inv order%r.
    + field;smt (gt0_order lt_fromint).
    have <- : Pr[Ad1.MainE(Addh0).main() @ &m : res] = Pr[DDH0_ex(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- : Pr[Ad1.MainE(Addh1).main() @ &m : res] = Pr[DDH1_ex(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- : Pr[Ad1.Main(Addh0).main() @ &m : res] = Pr[DDH0(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- /# : Pr[Ad1.Main(Addh1).main() @ &m : res] = Pr[DDH1(A).main() @ &m : res].
    by byequiv => //;proc;inline *;sim;auto.
  qed.
  proof.
    have /= H0 := Ad1.pr_abs Addh0 a1_ll _ &m (fun b _ => b).
    proc.
    call A_ll.
    rnd.
    skip.
    rewrite /= dt_ll.
    trivial.
    have /= H1 := Ad1.pr_abs Addh1 a1_ll _ &m (fun b _ => b).
    proc.
    call A_ll.
    do !rnd.
    skip.
    rewrite /= dt_ll.
    trivial.
    have -> : 2%r / order%r = inv order%r + inv order%r.
    field.
    smt (gt0_order lt_fromint).
    have <- : Pr[Ad1.MainE(Addh0).main() @ &m : res] = Pr[DDH0_ex(A).main() @ &m : res].
    byequiv.
    move=> //.
    proc.
    inline *.
    sim.
    auto.
    move=> //.
    move=> //.
    trivial.
    have <- : Pr[Ad1.MainE(Addh1).main() @ &m : res] = Pr[DDH1_ex(A).main() @ &m : res].
    byequiv.
    move=> //.
    proc.
    inline *.
    sim.
    auto.
    move=> //.
    move=> //.
    trivial.
    have <- : Pr[Ad1.Main(Addh0).main() @ &m : res] = Pr[DDH0(A).main() @ &m : res].
    byequiv.
    move=> //.
    proc.
    inline *.
    sim.
    move=> //.
    move=> //.
    trivial.
    have <- /# : Pr[Ad1.Main(Addh1).main() @ &m : res] = Pr[DDH1(A).main() @ &m : res].
    byequiv.
    move=> //.
    proc.
    inline *.
    sim.
    move=> //.
    move=> //.
    trivial.
  qed.
  proof.
byphoare => //.
proc.
swap 3 3.
swap 2 3.
rnd (pred1 b').
rnd.
call (_ : true).
apply Alg_result_ll.
while (i <= numq) (numq - i).
move => z.
wp.
call (_ : true).
apply Alg_answer_ll.
wp.
call (_ : true).
apply Alg_query_ll.
auto; smt().
call Alg_init_ll.
auto; progress.
smt(ge0_numq).
smt().
rewrite dbool1E /#.
smt().
rewrite weight_dinter.
smt(ge1_arity).
qed.
proof.
rewrite -(G2_G3 &m) (GOr_G2 &m).
qed.