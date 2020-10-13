require import Bool Distr Int Real DBool.

module Coins ={
  proc game1() : bool * bool ={
    var x,y : bool;
    x = true;
    y = true;	
    while (x = y){
      x <$ dbool;
      y <$ dbool;
    }
    return (x,y);
  }

  proc game2() : bool * bool ={
    var x : bool;
    x <$ dbool;
    return (x,!x);
  }
}.

lemma game1truetrue &m1 : 0%r = Pr[Coins.game1() @ &m1 : res = (true,true)].
    proof.
      byphoare => //.
      hoare.
      proc.
      auto.
      seq 2: true => //.
      while true => //.
      skip.
      smt.
    qed.
    
lemma game1falsefalse &m1 : 0%r = Pr[Coins.game1() @ &m1 : res = (false,false)].
    proof.
      byphoare => //.
      hoare.
      proc.
      auto.
      seq 2: true => //.
      while true => //.
      skip.
      smt.
    qed.

lemma game2truetrue &m1 : 0%r = Pr[Coins.game2() @ &m1 : res = (true,true)].
    proof.
      byphoare => //.
      hoare.
      proc.
      auto.
      smt.
    qed.

lemma game2falsefalse &m1 : 0%r = Pr[Coins.game2() @ &m1 : res = (false,false)].
    proof.
      byphoare => //.
      hoare.
      proc.
      auto.
      smt.
    qed.
  

lemma game1truefalse &m1 : 1%r/2%r = Pr[Coins.game1() @ &m1 : res = (true,false)].
    proof.
    byphoare => //.
      proc.
      seq 2: (x=y) (1%r / 2%r) => //.
      by wp. trivial.
    while true (if (x=y) then 1 else 0) 1 (1%r / 2%r) => //.
      smt.
    move => H .    
      seq 1: true (1%r / 2%r) => //.
      rnd. skip. smt.
      seq 1: true (1%r / 2%r).
      rnd. skip. smt.
      rnd. skip. smt.
      apply H.
  hoare.
      rnd. skip. smt.
      smt.
      seq 1: true => //.
      rnd. skip. smt.
      rnd. skip. smt.
      progress.
      smt.
      seq 1: (z = 1) (1%r / 2%r) => //.
      rnd. skip. smt.
      rnd (fun h => h <> x). skip. smt.
  hoare.
      wp. skip. smt.
  qed.

lemma game1falsetrue &m1 : 1%r/2%r = Pr[Coins.game1() @ &m1 : res = (false,true)].
    proof.
    byphoare => //.
      proc.
      seq 2: (x=y) (1%r / 2%r) => //.
      by wp. trivial.
    while true (if (x=y) then 1 else 0) 1 (1%r / 2%r) => //.
      smt.
    move => H .    
      seq 1: true (1%r / 2%r) => //.
      rnd. skip. smt.
      seq 1: true (1%r / 2%r).
      rnd. skip. smt.
      rnd. skip. smt.
      apply H.
  hoare.
      rnd. skip. smt.
      smt.
      seq 1: true => //.
      rnd. skip. smt.
      rnd. skip. smt.
      progress.
      smt.
      seq 1: (z = 1) (1%r / 2%r) => //.
      rnd. skip. smt.
      rnd (fun h => h <> x). skip. smt.
  hoare.
      wp. skip. smt.
  qed.

  
lemma game2truefalse &m1 : (1%r/2%r) = Pr[Coins.game2() @ &m1 : res = (true,false)].
    proof.
      byphoare => //.
      proc.
      rnd. skip.
      move=> _ hp1.
      split.
      smt (dboolE).
      move => hp4 hp2 hp3.
      smt.
    qed.  

lemma game2falsetrue &m1 : (1%r/2%r) = Pr[Coins.game2() @ &m1 : res = (false,true)].
    proof.
      byphoare => //.
      proc.
      rnd. skip.
      move=> _ hp1.
      split.
      smt (dboolE).
      move => hp4 hp2 hp3.
      smt.
    qed.  
            
lemma result: equiv [Coins.game1 ~ Coins.game2 : true ==> ={res}].
    proof.
    bypr (res{1}) (res{2}) => // &m1 &m2 a.
    case(a) => at1 at2.
    case(at1) => at1t.
    case(at2) => at2t.
      have <-: 0%r = Pr[Coins.game1() @ &m1 : res = (true,true)].
      smt(game1truetrue).
      have <-: 0%r = Pr[Coins.game2() @ &m2 : res = (true,true)].
      smt(game2truetrue).
    trivial.
      have <-: 1%r/2%r = Pr[Coins.game1() @ &m1 : res = (true,false)].
      smt(game1truefalse).
      have <-: 1%r/2%r = Pr[Coins.game2() @ &m2 : res = (true,false)].
      smt(game2truefalse).
    trivial.
    case(at2) => at2f.
      have <-: 1%r/2%r = Pr[Coins.game1() @ &m1 : res = (false,true)].
      smt(game1falsetrue).
      have <-: 1%r/2%r = Pr[Coins.game2() @ &m2 : res = (false,true)].
      smt(game2falsetrue).
    trivial. 
      have <-: 0%r = Pr[Coins.game1() @ &m1 : res = (false,false)].
      smt(game1falsefalse).
      have <-: 0%r = Pr[Coins.game2() @ &m2 : res = (false,false)].
      smt(game2falsefalse).
    trivial.
   qed.
    
