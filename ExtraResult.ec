require import AllCore Bool Distr Int Real DBool List FSet DInterval.

  (* General result on map *)

   lemma nth_map_myway (f : 'a -> 'b)(s1 : 'a list) x x1:
           mem s1 x => nth x1 (map f s1) (index x s1) = f x.
       proof.
       move => hp1.
         have hp2: 0 <= index x s1 < size s1.
         smt.
         have hp4: x = nth x s1 (index x s1).
         smt.
         rewrite hp4.
       smt.
       qed.
         
     lemma onth_map_myway (f : 'a -> 'b)(s1 : 'a list) x:
           mem s1 x => onth (map f s1) (index x s1) = Some (f x).
         proof.
         move=>hp1.         
           have: nth (f x) (map f s1) (index x s1) = f x.
           smt(nth_map_myway).
         smt.
         qed.
  
  (* End result on map *)

  (* General result on list *)
       lemma inziplists (x : 'a list)(y : 'b list)(x0 : 'a)(y0 : 'b) &m : y0 \in y =>
           size y = size x => (exists x1, (x1, y0) \in zip x y).
  proof.      
    move => *.
    exists (nth x0 x (index y0 y)).
    by have: y0 = nth y0 y (index y0 y); smt.
qed.


lemma assoclist (x : 'a list) (f : 'a -> 'b) (x0 : 'a) : x0 \in x =>
    oget (assoc (zip x (map f x)) x0) = f x0.
    proof.
    move => *.    
      by smt. qed.

lemma assocthreefunb  (l1: 'a list)(l3: 'c list)(f: ('b*'c) -> 'd)(g:'a -> 'b)(el1:'a)(el2:'c): el1 \in l1 =>
    size l1 = size l3 =>
    nth (f (g el1, oget (onth l3 (index el1 l1)))) (map f (zip (map g l1) l3)) (index el1 l1) = f (g el1, oget (onth l3 (index el1 l1))).
      proof.
      move => *.
        have hp4: size l1 = size (map f(zip (map g l1) l3)).
        smt.
       by have hp7: nth (f (g el1, oget (onth l3 (index el1 l1)))) (map f (zip (map g l1) l3))
      (index el1 l1) = f (nth (g el1) (map g l1) (index el1 l1), nth el2 l3 (index el1 l1)); smt.
      qed.

    lemma assocthreefun (l1: 'a list)(l3: 'c list)(f: ('b*'c) -> 'd)(g:'a -> 'b)(el1:'a): el1 \in l1 =>
        size l1 = size l3 =>
        assoc( zip l1 (map f (zip (map g l1) l3))) el1 = Some(f( g el1, oget(assoc(zip l1 l3) el1))).
      proof.
      move => hp1 hp2.
        rewrite assoc_zip.
        smt.
        rewrite assoc_zip => //.
        have hp3: nth (f (g el1, oget (onth l3 (index el1 l1)))) (map f (zip (map g l1) l3)) (index el1 l1) = f (g el1, oget (onth l3 (index el1 l1))).
        smt(assocthreefunb).
      smt.      
    qed.

  lemma assocthreefunv2 (l1: 'a list)(l2: 'b list)(l3: 'c list)(f: ('b*'c) -> 'd)(el1:'a)(el2:'b)(el3:'c) : el1 \in l1 =>
      size l1 = size l2 =>
      size l1 = size l3 =>
      assoc (zip l1 (map f (zip l2 l3))) el1 = Some (f ( oget (assoc (zip l1 l2) el1), oget (assoc (zip l1 l3) el1))).
      proof.
      move => hp1 samesize1 samesize2.
        rewrite !assoc_zip. smt. smt. smt.
        have hp2: nth ((f (oget (onth l2 (index el1 l1)), oget (onth l3 (index el1 l1))))) (map f (zip l2 l3)) (index el1 l1) = f (oget (onth l2 (index el1 l1)), oget (onth l3 (index el1 l1))).
        have hp7: nth (f (oget (onth l2 (index el1 l1)), oget (onth l3 (index el1 l1)))) (map f (zip l2 l3)) (index el1 l1) = f (nth (el2) l2 (index el1 l1), nth el3 l3 (index el1 l1)). smt. smt. smt.      
      qed.

    lemma sndofzip (al : 'a list)(bl : 'b list)(n : int) : size al = size bl =>
        0 <= n < size al =>
      oget (onth al n) = snd (oget (onth (zip bl al) n)). by smt. qed.

  lemma unzip1assoc (al :'a list)(bl : ('b * 'c) list)(el: 'a) : size al = size bl => el \in al =>
      fst (oget (assoc (zip al bl) el)) = oget (assoc (zip al (unzip1 bl)) el).
      proof.
      move => samesize inlist.
      rewrite assoc_zip => //.
      rewrite assoc_zip.
        smt.
      smt.
      qed.
    
    lemma problematickindoflist (al : 'a list)(bl : (('b * 'c) * ('d * 'e)) list)(el: 'a) : size al = size bl =>
        el \in al =>
        fst(fst(oget(assoc(zip al bl) el))) = oget (assoc (zip al (unzip1 (unzip1 bl))) el).
      proof.
        move => *.
        rewrite unzip1assoc => //.
        rewrite unzip1assoc => //.
        smt.
      qed.


    lemma assocmapfun (al : 'a list) (ael : 'a)(ael2 :'a) (b1 :'b) (b2 : 'b)(b3 : 'b) : ael \in al =>
    assoc (zip (al) (map (fun (x : 'a) =>
              if x = ael then b1
          else if x = ael2 then b2 else b3) (al))) ael = Some(b1). by smt. qed.

    lemma assocmapfun2 (al : 'a list) (ael : 'a)(ael2 :'a) (b1 :'b) (b2 : 'b)(b3 : 'b) : ael \in al =>
        ael <> ael2 =>
    assoc (zip (al) (map (fun (x : 'a) =>
              if x = ael2 then b1
          else if x = ael then b2 else b3) (al))) ael = Some(b2).
    proof. by smt. qed.



      (* End of general result on lists *)



