require import AllCore Bool Distr Int Real DBool List FSet DInterval ExtraResult.

require (*--*) SigmaProtocol.

pragma -oldip.
pragma +implicits.

(*Defining the basic types*)

type node.
type color.
type secret.
type commitment.


(*Define the Graph as a node fset: uniqueness of node *)
const nodeGraph: node fset.

(*const numNodes: int = size (elems nodeGraph).*)

(*Colors*)
const Red:color.
const Blue:color.
const Green:color.
const Black:color.

(*Require colors are differents *)
axiom diff_color: (Red <> Blue) /\ (Red <> Green) /\ (Blue <> Green) /\
    (Red <> Black) /\ (Green <> Black) /\ (Blue <> Black).

(*Define permutation*)
op perm (p:int)(c:color) = (p=1) ? c :
((p=2) ? ((c=Red) ? Blue : ((c=Blue) ? Green : Red)) :
((p=3) ? ((c=Red) ? Green : ((c=Blue) ? Red : Blue)) :
((p=4) ? ((c=Red) ? Red : ((c=Blue) ? Green : Blue)) :
((p=5) ? ((c=Red) ? Green : ((c=Blue) ? Blue : Red)) :
((p=6) ? ((c=Red) ? Blue : ((c=Blue) ? Red : Green)) :
Red))))).

(*Secret*)
const ChallengeRefused : secret.

op dsecret: {secret distr | is_lossless dsecret /\ is_funiform dsecret }
     as dsecret_llfuni.

op nodetosec: node -> secret distr = fun x => dsecret.

axiom onlyrealsecret: forall (a: secret), a \in dsecret => a <> ChallengeRefused.
axiom everyrealsecret: forall (a: secret), a <> ChallengeRefused => a \in dsecret.


(*Commitments*)
const NoCommit : commitment.

(* Represent the commitment functions *)
op commit: color * secret -> commitment.

(*axiom bindingcommitment: forall (s:secret, c1, c2:color),
    commit (c1,s) = commit (c2,s) => c1 = c2. *)

(*Missing the Hiding*)

(*Model the edge as operator*)

op edge: node -> node -> bool.

  (*Property of edge*)
axiom edge_in_graph: forall(n1,n2:node),
    !(n1 \in (elems nodeGraph) /\ n2 \in (elems nodeGraph)) => ! (edge n1 n2).

  (*implies edge n1 n2 => n1 /\ n2 \in elems nodeGraph*)

(* Note: given I can revert n1 and n2, this works as IFF *)
axiom symmetric_edge: forall(n1,n2:node), edge n1 n2 => edge n2 n1.


op dedge: (node * node) distr.

axiom dedge_ll : is_lossless dedge.

axiom onlyedgeingraph: forall (a: node * node), a \in dedge => edge (fst a) (snd a).

axiom everyedgeingraph: forall (a: node * node), edge (fst a) (snd a) => a \in dedge.

const edge_list : (node * node) list.

axiom alltheedges : forall(n1,n2:node), edge n1 n2 => (n1,n2) \in edge_list.

axiom onlytheedges : forall(n : node * node), n \in edge_list => edge (fst n) (snd n).

axiom onlyonce : uniq edge_list.



(* We assume that graph is 3-Colorable and we've a witness, 
    that is a 3-Coloration of the graph *)
op witness: node -> color.

op witnesslist: node list -> color list = fun (nodelist: node list) =>
     map witness nodelist.

axiom threecol1: forall (n:node), n \in (elems nodeGraph) =>
    (witness n = Green \/ witness n = Red \/ witness n = Blue).

axiom threecol2: forall (n1,n2:node), (edge n1 n2) => (witness(n1) <> witness(n2)).


(*Working operator to simplify the writings*)
op onlythreecol(c:color) : bool = c = Red \/ c = Green \/ c = Blue.

(* operator checking the requirements of protocol *)
op Rel (nl : node list) (cl : color list) : bool = (size nl = size cl) /\
    forall (n1, n2: node), n1 \in nl => n2 \in nl => edge n1 n2 =>
    oget(assoc (zip nl cl) n1) <> oget(assoc (zip nl cl) n2) /\
    onlythreecol (oget(assoc (zip nl cl) n1)) /\
    onlythreecol (oget(assoc(zip nl cl) n2)).

op verifyasop (nodelist: node list, commlist: commitment list, e: node * node,
    response: (color * color) * (secret * secret)) : bool = (
  onlythreecol (fst (fst response)) /\
  onlythreecol (snd (fst response)) /\
  fst (snd response) <> ChallengeRefused /\
  snd (snd response) <> ChallengeRefused /\
  fst (fst response) <> snd (fst response) /\
  commit (fst (fst response),fst (snd response)) =
    oget (assoc (zip nodelist commlist) (fst e)) /\
  commit (snd (fst response),snd (snd response)) =
    oget (assoc (zip nodelist commlist) (snd e))).


  (*import the general SigmaProtocol library*)
clone import SigmaProtocol as SP with
  type SigmaProtocol.statement <- node list,
  type SigmaProtocol.witness   <- color list,
  type SigmaProtocol.message   <- commitment list,
  type SigmaProtocol.secret    <- secret list,
  type SigmaProtocol.challenge <- node * node,
  type SigmaProtocol.response  <- (color * color) * (secret * secret),
  op   SigmaProtocol.R         = Rel, 
  op   SigmaProtocol.de        = dedge.
  export SigmaProtocol.


module ThreeColProver : SigmaScheme = {
  (* It returns "statement" (node list) * witness (color list) *)
  proc gen() : node list * color list = {
    var p : int;
    p <$ [1..6];    
    return (elems nodeGraph, map (fun x:node => perm p (witness x)) (elems nodeGraph));
  }

  (* It returns "message" (commitment list) * secret (secret list) *)
  proc commit(nodelist: node list, colorlist: color list) :
      commitment list * secret list ={
    var seclist : secret list;
    var buildseclist : secret list distr = djoin(map (fun x => nodetosec x) nodelist);
    seclist =$ buildseclist;
    return (map commit (zip colorlist seclist), seclist);
  }

  proc test(nodelist: node list, commlist: commitment list): node * node = {
    var edge: (node*node);
    edge =$ dedge;
    return edge;
  }
  
     
   (* input is of type "challenge", pair of node, and output is "response" type, 
      color pair * secret pair *)
  proc respond (nodecoll: node list * color list,
      commsecl: commitment list * secret list, edge:node*node) :
      (color * color) * (secret * secret) = {
    var out : (color * color) * (secret * secret); 
    var nodecol : (node * color) list = zip (fst nodecoll) (snd nodecoll);
    var nodesec : (node * secret) list = zip (fst nodecoll) (snd commsecl);
    if (edge (fst edge) (snd edge)) {
      out = ((oget (assoc nodecol (fst edge)), oget (assoc nodecol (snd edge))),
        (oget (assoc nodesec (fst edge)),oget (assoc nodesec (snd edge))));
    } else {
      out = ((Black, Black), (ChallengeRefused, ChallengeRefused));
    }
    return out;
  }

  proc verify (nodelist: node list, commlist: commitment list,
      e: node * node, response: (color * color) * (secret * secret)) : bool = {
    var c1 : color = fst (fst response);
    var c2 : color = snd (fst response);
    var s1 : secret = fst (snd response);
    var s2 : secret = snd (snd response);
    var commit1 : commitment = oget (assoc (zip nodelist commlist) (fst e));
    var commit2 : commitment = oget (assoc (zip nodelist commlist) (snd e));
    var out : bool = false;
    if (!( onlythreecol c1) \/ !(onlythreecol c2) \/ s1 = ChallengeRefused \/
      s2 = ChallengeRefused \/ c1 = c2 \/ commit(c1,s1) <> commit1 \/
      commit (c2,s2) <> commit2) {
        out = false;
    } else {
        out = true;
      }
    return out;    
  }  
}.

      


    (*Here start the proofs*)
lemma mydjoin_ll: forall (x:node list), weight (djoinmap nodetosec x) = 1%r.
  proof.  
    move =>*.
    rewrite djoin_ll => //.
    smt.
  qed.

  (* Completeness is lossless *)
lemma threecol_proof_of_knowledge_completeness_ll:
    islossless Completeness(ThreeColProver).main.
  proof.
    islossless.
    apply dedge_ll.
    by rewrite mydjoin_ll.
  qed.



      (*Working lemmas to prove completeness*)
lemma lem1 : forall (v: node*node), v \in dedge =>
    (fst v) \in elems nodeGraph /\ (snd v) \in elems nodeGraph.
  proof.
    move => hp1 hp2.
    apply onlyedgeingraph in hp2.
    smt(edge_in_graph).
  qed.
      
lemma lem2 h c v &m: h = elems nodeGraph => R h c => v \in dedge =>
    onlythreecol(oget (assoc (zip h c) (fst v))) /\
    onlythreecol( oget (assoc (zip h c) (snd v))).
  proof.
    rewrite /R /Rl.
    move => hprel.
    move => hp1 hp2.
    rewrite /Rel in hp1.
    smt.
  qed.
  
      
lemma indsecret x s a &m : x = elems nodeGraph =>
    s \in djoinmap nodetosec x => a \in s => a \in dsecret.
  proof.
    move=> hp1 hp2 hp3.
    rewrite supp_djoinmap in hp2.      
    elim hp2.
    move => hp2 hp4.
    rewrite allP in hp4.
    have hp5: a \in s => size x = size s => (exists x0, (x0, a) \in zip x s).
    smt (inziplists).
    smt.
  qed.
    
lemma secretindist x s v &m : x = elems nodeGraph =>
    s \in djoinmap nodetosec x => predT s => v \in dedge =>
    oget (assoc (zip x s) (fst v)) \in dsecret /\
    oget (assoc (zip x s) (snd v)) \in dsecret.
  proof.
    move => hp1 hp2 hp3 hp4.
    have eqze: size x = size s.
    smt.
    have notNone: assoc (zip x s) (fst v) <> None /\ assoc (zip x s) (snd v) <> None.
    apply lem1 in hp4.
    do 2!rewrite assocTP.
    rewrite unzip1_zip.
    smt.
    smt.
    have hp5: oget(assoc (zip x s) (fst v)) \in s /\
      oget(assoc (zip x s) (snd v)) \in s.
    split.
    smt.
    smt.
    split.
    smt(indsecret).
    smt(indsecret).    
  qed.

 lemma threecol_proof_of_knowledge_completeness h w' &m:
    h = elems nodeGraph => R h w' =>
    Pr[Completeness(ThreeColProver).main(h, w') @ &m : res] = 1%r. 
  proof.     
    rewrite /R /Rl; move => elements hprel.
    byphoare (_: h = x /\ w' = w ==> _) => //. 
    proc.
    inline*; wp => /=. rewrite /snd /=.
    auto => &hr />.
    rewrite dedge_ll.
    have: weight (djoinmap nodetosec x{hr}) = 1%r.
    smt(mydjoin_ll).
    move => hpdjoin.
    rewrite hpdjoin.
    simplify.
    move => /> s ds ps v dv pv.
    rewrite onlyedgeingraph => //.
    split => //; move => _.
    (* Change the goal form to be able to split it *)
    have <-: (oget (assoc (zip x{hr} w{hr}) (fst v)) <> Black /\
    oget (assoc (zip x{hr} w{hr}) (snd v)) <> Black /\
    oget (assoc (zip x{hr} s) (fst v)) <> ChallengeRefused /\
    oget (assoc (zip x{hr} s) (snd v)) <> ChallengeRefused /\
    oget (assoc (zip x{hr} w{hr}) (fst v)) <>
      oget (assoc (zip x{hr} w{hr}) (snd v)) /\
    commit (oget (assoc (zip x{hr} w{hr}) v.`1), oget (assoc (zip x{hr} s) v.`1)) =
      oget (assoc (zip x{hr} (map commit (zip w{hr} s))) v.`1) /\
    commit (oget (assoc (zip x{hr} w{hr}) v.`2), oget (assoc (zip x{hr} s) v.`2)) =
      oget (assoc (zip x{hr} (map commit (zip w{hr} s))) v.`2)) =
    ! (!onlythreecol (oget (assoc (zip x{hr} w{hr}) v.`1)) \/
      !onlythreecol (oget (assoc (zip x{hr} w{hr}) v.`2)) \/
      oget (assoc (zip x{hr} s) v.`1) = ChallengeRefused \/
      oget (assoc (zip x{hr} s) v.`2) = ChallengeRefused \/
      oget (assoc (zip x{hr} w{hr}) v.`1) = oget (assoc (zip x{hr} w{hr}) v.`2) \/
      commit (oget (assoc (zip x{hr} w{hr}) v.`1), oget (assoc (zip x{hr} s) v.`1)) <>
        oget (assoc (zip x{hr} (map commit (zip w{hr} s))) v.`1) \/
      commit (oget (assoc (zip x{hr} w{hr}) v.`2), oget (assoc (zip x{hr} s) v.`2)) <>
    oget (assoc (zip x{hr} (map commit (zip w{hr} s))) v.`2)).
    smt.

    split. smt (lem2 diff_color).
    split. smt (lem2 diff_color).
    split. smt (secretindist onlyrealsecret).
    split. smt (secretindist onlyrealsecret).
    split. smt.
    apply lem1 in dv. 
    have hp4: size x{hr} = size w{hr} /\ size x{hr} = size s.
    smt.
    split.
    smt(assocthreefunv2).
    smt(assocthreefunv2).
  qed.

  (*Operator to simplify notation*)
op fstcolor (y : (node * node) * ((color * color) * (secret * secret))) :
  color = fst (fst (snd y)).
op sndcolor (y : (node * node) * ((color * color) * (secret * secret))) :
color = snd (fst (snd y)).

module Extractability (S:SigmaScheme)= {
  proc extract(h: node list, a: commitment list, chl1: (node * node) list,
  zl1: ((color * color) * (secret * secret)) list, chl2: (node * node) list,
  zl2: ((color * color) * (secret * secret)) list) : color list option = {
  var s, vl1, vl2, wl1, wl2, c1, c2,  c3, c4, c5;
    wl1 = zip chl1 zl1;
    wl2 = zip chl2 zl2;

  (* These are lists of true IFF for each chl I get an answer satisfying the property and the commitment scheme!! *)
    vl1 = map (fun (x: ((node * node) * ((color * color) * (secret * secret)))) =>
      verifyasop h a (fst x) (snd x)) wl1;
    vl2 = map (fun (x: ((node * node) * ((color * color) * (secret * secret)))) =>
      verifyasop h a (fst x) (snd x)) wl2;

  (* REQUIREMENTS: *)
  (* chl1 has to contain all the nodes of h, ordered *)
    c1 = pred1 (unzip1 chl1) h;

  (* chl2 has to conatin all the edges *)
    c2 = pred1 chl2 edge_list;

  (* All the challenges have to be verified *)
    c3 = pred1 (nseq (size vl1) true) vl1;

    c4 = pred1 (nseq (size vl2) true) vl2;

  (*Each time a nodes appear in a chl, its corresponding color 
    has to be the one of wl1 *)
    c5 =  forall(y : (node * node) * ((color * color) * (secret * secret))),
      y \in wl2 =>
      fstcolor y = fstcolor (oget(onth wl1 (index (fst (fst y)) h))) /\
      sndcolor y = fstcolor (oget(onth wl1 (index (snd (fst y)) h)));    
    
   (* If all the conditions are satisfied, I can safely build my witness *)

  if (c1 /\ c2 /\ c3 /\ c4 /\ c5) {
       s = Some(unzip1(unzip1 zl1));
   } else {
      s = None;
    }

        return s;
  }
}.




    
    
lemma threecol_extractability h' a' chl1' zl1' chl2'  zl2' &m:
    h' = elems nodeGraph  =>
    size h' = size zl1' =>
    size chl2' = size zl2' =>
    pred1 (unzip1 chl1') h' =>
    pred1 chl2'  edge_list =>
    pred1 (nseq (size (zip chl1' zl1')) true)
      (map (fun (x: ((node * node) * ((color * color) * (secret * secret)))) =>
        verifyasop h' a' (fst x) (snd x)) (zip chl1' zl1')) =>
    pred1 (nseq (size (zip chl2' zl2')) true)
      (map (fun (x: ((node * node) * ((color * color) * (secret * secret)))) =>
        verifyasop h' a' (fst x) (snd x)) (zip chl2' zl2')) =>
    (forall(y : (node * node) * ((color * color) * (secret * secret))),
      y \in (zip chl2'  zl2') =>
      fstcolor y = fstcolor (oget(onth (zip chl1'  zl1') (index (fst (fst y)) h'))) /\
      sndcolor y = fstcolor (oget(onth (zip chl1'  zl1') (index (snd (fst y)) h')))) =>
    Pr[Extractability(ThreeColProver).extract(h', a', chl1', zl1', chl2', zl2') @ &m :
      (res <> None /\ R h' (oget res))] = 1%r.
  proof.
    move => nodelist samesize samesize2 chl1isnodelist chl2isedgelist chl1verified
      chl2verified coherentcoloration2.
    byphoare (_ : h = h' /\ a = a' /\ chl1 = chl1' /\ zl1 = zl1' /\ chl2 = chl2'
      /\ zl2 = zl2'  ==> _) => //.
    proc.
    auto.
    rewrite /R /R_DL => &m1 hp1 /=.
    rewrite /Rl.
    elim hp1; move => hp1 hp2.
    elim hp2; move => hp2 hp3.
    elim hp3; move => hp3 hp4.
    elim hp4; move => hp4 hp5.
    elim hp5; move => hp5 hp6.       
    rewrite hp1 hp2 hp3 hp4 hp5 hp6.
    split.  
    split.
    exact chl1isnodelist.
    split.    
    exact chl2isedgelist.
    split.
    smt.
    split.
    smt.
    exact coherentcoloration2.

    move => preconditions_true.
    rewrite /Rel.
    split.      
    smt. 
    move => n1 n2 n1inh n2inh edgen1n2.
  
    have edgeinlist: (n1,n2) \in chl2'.
    smt.
  
    have responsetoedgeinlist: oget(assoc (zip chl2' zl2') (n1,n2)) \in zl2'.
    have <-: onth zl2' (index (n1,n2) chl2') = assoc (zip chl2' zl2') (n1, n2).
    smt.
    smt.

    have allchallengestrue: forall (el: ((node * node) *
      ((color * color) * (secret* secret)))), el \in (zip chl2' zl2') =>
      true = verifyasop h' a' (fst el) (snd el).
    move => el inzip.
    have tosolve: (verifyasop h' a' (fst el) (snd el)) \in
      map (fun (x : (node * node) * ((color * color) * (secret * secret))) =>
      verifyasop h' a' x.`1 x.`2) (zip chl2' zl2').
    smt.    
    smt.

    have verifyasopn1n2ok : verifyasop h' a' (n1,n2)
      (oget(assoc (zip chl2' zl2') (n1,n2))).
    have tosolve : ((n1,n2),(oget (assoc (zip chl2' zl2') (n1, n2)))) \in
      zip chl2' zl2'.
    have <-: onth zl2' (index (n1,n2) chl2') = assoc (zip chl2' zl2') (n1, n2).
    smt.    
    smt.
    smt.

    have coherentcoloration : (forall (n1: node), n1 \in h' =>
      forall (n2 : node), n2 \in h' /\ (n1,n2) \in chl2' => 
      fst (fst (oget (assoc (zip chl2' zl2') (n1,n2)))) =
      oget (assoc (zip h' (unzip1 (unzip1 zl1'))) n1)).
    move => node1 node1inh node2 node2inh.
    elim node2inh => node2inh edgeinchl.    

    have <-: fst(fst(snd(oget(onth (zip chl1' zl1') (index node1 h'))))) =
      oget(assoc (zip h' (unzip1 (unzip1 zl1'))) node1).
    rewrite -problematickindoflist => //.
    have <-: (oget (onth  zl1' (index node1 h'))).`1.`1 =
      (oget (onth (zip chl1' zl1') (index node1 h'))).`2.`1.`1.
    smt.    
    smt.

    have <-: fst (fst (snd ((node1,node2),
      (oget (assoc (zip chl2' zl2') (node1, node2)))))) =
      (oget (assoc (zip chl2' zl2') (node1, node2))).`1.`1.
    smt.    
    have toparse : fst (fst ((node1,node2),
      (oget (assoc (zip chl2' zl2') (node1, node2)))))  =
      node1.
    smt.
    rewrite - {-1 2} toparse => //.
    have lasthp : ((node1, node2), oget (assoc (zip chl2' zl2') (node1, node2))) \in
      zip chl2' zl2'.
    have <-: onth zl2' (index (node1,node2) chl2') =
      assoc (zip chl2' zl2') (node1, node2).
    smt.    
    smt.
    smt.

    have coherentcolorationsnd : (forall (n2: node), n2 \in h' =>
      forall (n1 : node), n1 \in h' /\ (n1,n2) \in chl2' =>
      snd (fst (oget (assoc (zip chl2' zl2') (n1,n2)))) =
      oget (assoc (zip h' (unzip1 (unzip1 zl1'))) n2)).
    have reverseedge: (n2, n1) \in chl2'.
    smt.
    move => node2 node2inh node1 node1inh.
    elim node1inh => node1inh edgeinchl.
    have <-: fst(fst(snd(oget(onth (zip chl1' zl1') (index node2 h'))))) =
      oget(assoc (zip h' (unzip1 (unzip1 zl1'))) node2).
    rewrite -problematickindoflist => //.
    have <-: (oget (onth  zl1' (index node2 h'))).`1.`1 =
      (oget (onth (zip chl1' zl1') (index node2 h'))).`2.`1.`1.
    smt.    
    smt.
    have <-: snd (fst (snd ((node1,node2),
      (oget (assoc (zip chl2' zl2') (node1, node2)))))) =
      (oget (assoc (zip chl2' zl2') (node1, node2))).`1.`2.
    smt.    
    have toparse : snd (fst ((node1,node2),
      (oget (assoc (zip chl2' zl2') (node1, node2)))))  = node2.
    smt.
    rewrite - {-1 2} toparse => //.
    have lasthp : ((node1, node2), oget (assoc (zip chl2' zl2') (node1, node2))) \in
      zip chl2' zl2'.
    have <-: onth zl2' (index (node1,node2) chl2') =
      assoc (zip chl2' zl2') (node1, node2).
    smt.    
    smt.
    smt.

    have <-: (oget (assoc (zip chl2' zl2') (n1,n2))).`1.`1 =
      oget (assoc (zip h' (unzip1 (unzip1 zl1'))) n1).    
    rewrite coherentcoloration => //.
    have <-: (oget (assoc (zip chl2' zl2') (n1,n2))).`1.`2 =
      oget (assoc (zip h' (unzip1 (unzip1 zl1'))) n2).
    rewrite coherentcolorationsnd => //.    
    smt.
  qed.    



(* This is in itself an interesting lemma! 
      have uselessbutinterestinglemma: forall (n1 : node, n2: node), (n1,n2) \in chl2' => (oget (assoc (zip chl2' zl2') (n1, n2))).`1.`1 = (oget (assoc (zip chl2' zl2') (n2, n1))).`1.`2.
move => node1 node2 edgein.
      rewrite coherentcoloration => //. smt. 
      smt.
      rewrite coherentcolorationsnd => //. smt.
    smt.
*)
