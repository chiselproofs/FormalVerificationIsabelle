theory "ParameterizedButterfly"
  imports Complex_Main
begin 

(* Proofs for the generator for a general form of BUTTERFLY circuit *)
(********************************************************************)
(* f and g represent subcomponents in the upper butterfly for 
   each next stage and in the lower butterfly for each next stage *)


(********** 1.Signals *************)
(**********************************)
(* Wire : wire (internal signal or primary input/output), 
   Reg : output of a flip-flop *)
datatype 't Signal = 
  Wire 't |
  Reg "'t Signal" 

primrec latency :: "'t Signal \<Rightarrow> nat" where
   "latency (Wire x) = 0" |
   "latency (Reg x) =  (latency x) + 1" 

primrec signal_value :: "'t Signal \<Rightarrow> 't" where
   "signal_value (Wire x) = x" |
   "signal_value (Reg x) =  signal_value x" 

(***** 2.Two inputs component with properties ****)
(*************************************************)

datatype ('t1,'t2) TwoInputsTrait =
  Tuple_of2 (Compute2 : "'t1 Signal \<times> 't1 Signal \<Rightarrow> 't2 Signal") 
            (Latency2 : nat)
            (Reliability2 : real)


(******** 3.Butterfly ********)
(*****************************)

(* datatype for modules that take 2 signal lists as input and *)
(* output a signal list (type of the Butterfly)               *)
datatype 't TwoListsTrait =
  Tuple_ofL (Compute : "'t Signal list \<Rightarrow> 't Signal list  \<Rightarrow> 't Signal list")
            (Latency : nat)
            (Reliability : real)

(* To group the elements of two lists 2 by 2 *)
fun group_signal_lists :: "'a Signal list \<Rightarrow> 'a Signal list \<Rightarrow> ('a Signal \<times> 'a Signal) list" where
   "group_signal_lists [] [] = []" |
   "group_signal_lists (x#l) [] = []" |
   "group_signal_lists [] (y#l) = []" |
   "group_signal_lists (x#l) (y#l2) = ((x,y)#(group_signal_lists l l2))"

(* To split a list into 2 parts of identical lengths *)
fun first :: "'a Signal list \<Rightarrow> nat \<Rightarrow> 'a Signal list" where
   "first l 0 = []" |
   "first [] (Suc n) = []" |
   "first (x#l) (Suc n) = x#(first l n)"

fun second :: "'a Signal list \<Rightarrow> nat \<Rightarrow> 'a Signal list" where
   "second l 0 = l" |
   "second [] (Suc n) = []" |
   "second (x#l) (Suc n) = second l n"

(* Elementary butterfly (2 signals as inputs)     *)
fun butterfly1 :: "('t Signal \<times> 't Signal \<Rightarrow> 't Signal) \<Rightarrow>
                   ('t Signal \<times> 't Signal \<Rightarrow> 't Signal) \<Rightarrow>
                   't Signal list \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list" where
   "butterfly1 f g a b = (f (hd a, hd b)) # (g (hd a, hd b)) # []"

fun latency_butterfly1 :: 
              "('t,'t) TwoInputsTrait \<Rightarrow> ('t,'t) TwoInputsTrait \<Rightarrow> nat" where
   "latency_butterfly1 tf tg = max (Latency2 tf) (Latency2 tg)"

lemma lemlatency_butterfly1 [simp] :
   "(Latency2 tf) = (Latency2 tg) \<Longrightarrow>
       latency_butterfly1 tf tg = (Latency2 tf)"
  apply (auto)
  done

(* Butterfly of size N (it has log2(N) stages)     *)
fun butterfly :: "nat \<Rightarrow> ('t Signal \<times> 't Signal \<Rightarrow> 't Signal)
                   \<Rightarrow> ('t Signal \<times> 't Signal \<Rightarrow> 't Signal)
                   \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list 
                   \<Rightarrow> 't Signal list" where
   "butterfly 0 f g l1 l2 = []" |
   "butterfly (Suc 0) f g l1 l2 = []" |
   "butterfly (Suc (Suc 0)) f g l1 l2 = (butterfly1 f g l1 l2)" |
   "butterfly N f g l1 l2 = (butterfly (N div 2) f g
                                 (first (map (\<lambda>(a,b).(f (a,b)))
                                             (group_signal_lists l1 l2)) (N div 4))
                                 (second (map (\<lambda>(a,b).(f (a,b)))
                                              (group_signal_lists l1 l2)) (N div 4)))
                             @
                             (butterfly (N div 2) f g
                                 (first (map (\<lambda>(a,b).(g (a,b)))
                                             (group_signal_lists l1 l2)) (N div 4))
                                 (second (map (\<lambda>(a,b).(g (a,b)))
                                              (group_signal_lists l1 l2)) (N div 4)))"

fun latency_butterfly :: 
          "nat \<Rightarrow> ('t,'t) TwoInputsTrait \<Rightarrow> ('t,'t) TwoInputsTrait \<Rightarrow> nat" where
   "latency_butterfly 0 tf tg = 0" |
   "latency_butterfly (Suc 0) tf tg = 0" |
   "latency_butterfly (Suc (Suc 0)) tf tg = (latency_butterfly1 tf tg)" |
   "latency_butterfly N tf tg = (latency_butterfly (N div 2) tf tg) 
                                 + (max (Latency2 tf) (Latency2 tg))"
(* in fact latencies of tf and tg should be equal *)

lemma lem1_latency_butterfly :
   "k \<ge> 0 \<and> (Latency2 tf) = (Latency2 tg) \<Longrightarrow>
       latency_butterfly (power 2 (Suc k)) tf tg = 
               latency_butterfly (power 2 k) tf tg + (Latency2 tf)"
   apply (induct k)
   apply (auto)
   apply (smt (verit) One_nat_def Suc_1 latency_butterfly.simps(3) lemlatency_butterfly1)
   by (smt (verit) add.commute add_cancel_left_left distrib_left_numeral latency_butterfly.elims latency_butterfly1.elims lemlatency_butterfly1 le_add1 mult.commute mult.left_commute mult_2 nat_less_le nonzero_mult_div_cancel_right not_less_eq numeral_1_eq_Suc_0 numeral_Bit0 plus_1_eq_Suc pos2 zero_neq_numeral)


(***** 4. Properties of the Butterfly ******)
(*******************************************)

(* Provided that f and g have the same latency l, the latency *)
(* of the Butterfly of size 2^k is k*l                        *)
lemma lemma_latency_butterfly :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f l r1))
                                    (Compute2 (Tuple_of2 g l r2)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f l r1) (Tuple_of2 g l r2))
                         r)
       = k * l"
   apply (induct k)
   apply (auto)
  by (metis (no_types, lifting) TwoInputsTrait.sel(2) add.commute gr0I latency_butterfly.simps(2) le_eq_less_or_eq lem1_latency_butterfly mult_is_0 mult_numeral_1_right nat_power_eq_Suc_0_iff numeral_1_eq_Suc_0 plus_1_eq_Suc power_Suc0_right power_add)

(* Provided that f and g have the same latency l, the latency *)
(* of the Butterfly of size 2^k equals l + the latency of the *)
(* Butterfly of size 2^(k-1)                                  *)
lemma lemma_latency_butterfly_size :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f l r1))
                                    (Compute2 (Tuple_of2 g l r2)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f l r1) (Tuple_of2 g l r2))
                         r)
       = (Latency (Tuple_ofL (butterfly (power 2 (k-1)) 
                                    (Compute2 (Tuple_of2 f l r1))
                                    (Compute2 (Tuple_of2 g l r2)))
                         (latency_butterfly (power 2 (k-1)) (Tuple_of2 f l r1) (Tuple_of2 g l r2))
                         rprime)) 
         + l"
  apply (auto)
  by (metis Suc_pred TwoInputsTrait.sel(2) bot_nat_0.not_eq_extremum le_eq_less_or_eq lem1_latency_butterfly)

(* If m>n, Latency of Butterfly with f2 and g2 of latency m =
           (Latency of Butterfly with f1 and g1 of latency n) + k*(m-n) *)
lemma lemma_latency_butterfly_m_n :
   "k > 0 \<and> m>n \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f2 m r12))
                                    (Compute2 (Tuple_of2 g2 m r22)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f2 m r12) (Tuple_of2 g2 m r22))
                         r)
       = (Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f1 n r11))
                                    (Compute2 (Tuple_of2 g1 n r21)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f1 n r11) (Tuple_of2 g1 n r21))
                         rprime)) 
        + (k*(m-n))"
  apply (simp add: lemma_latency_butterfly)
  by (metis TwoListsTrait.sel(2) add_diff_inverse_nat distrib_left lemma_latency_butterfly less_or_eq_imp_le linorder_not_less)


(***** 5. Examples of instantiations for specific functions f and g *****)
(************************************************************************)

fun f_plus :: "real Signal \<times> real Signal \<Rightarrow> real Signal" where
   "f_plus (x,y) = Reg (Wire ((signal_value x) + (signal_value y)))"

fun f_minus :: "real Signal \<times> real Signal \<Rightarrow> real Signal" where
   "f_minus (x,y) = Reg (Wire ((signal_value x) - (signal_value y)))"

lemma lemma_latency_butterfly_inst1 :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f_plus 1 r1))
                                    (Compute2 (Tuple_of2 f_minus 1 r2)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f_plus 1 r1) 
                                            (Tuple_of2 f_minus 1 r2))
                         r)
       = k"
  using lemma_latency_butterfly
  by (metis nat_mult_1_right)

lemma lemma_latency_butterfly_size_inst1 :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f_plus 1 r1))
                                    (Compute2 (Tuple_of2 f_minus 1 r2)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f_plus 1 r1) 
                                            (Tuple_of2 f_minus 1 r2))
                         r)
       = (Latency (Tuple_ofL (butterfly (power 2 (k-1)) 
                                    (Compute2 (Tuple_of2 f_plus 1 r1))
                                    (Compute2 (Tuple_of2 f_minus 1 r2)))
                         (latency_butterfly (power 2 (k-1)) (Tuple_of2 f_plus 1 r1) 
                                            (Tuple_of2 f_minus 1 r2))
                         rprime)) 
         + 1"
  using lemma_latency_butterfly_size
  by blast

lemma lemma_latency_butterfly_m_n_inst1 :
   "k > 0 \<and> m>1 \<Longrightarrow>
      Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f_plus_v2 m r12))
                                    (Compute2 (Tuple_of2 f_minus_v2 m r22)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f_plus_v2 m r12) 
                                            (Tuple_of2 f_minus_v2 m r22))
                         r)
       = (Latency (Tuple_ofL (butterfly (power 2 k) 
                                    (Compute2 (Tuple_of2 f_plus 1 r11))
                                    (Compute2 (Tuple_of2 f_minus 1 r21)))
                         (latency_butterfly (power 2 k) (Tuple_of2 f_plus 1 r11) 
                                            (Tuple_of2 f_minus 1 r21))
                         rprime)) 
        + (k*(m-1))"
  using lemma_latency_butterfly_m_n
  by blast

end
