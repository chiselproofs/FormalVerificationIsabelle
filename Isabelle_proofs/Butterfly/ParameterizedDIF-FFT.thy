theory "ParameterizedDIF-FFT"
  imports Complex_Main
begin 

(* Proofs for the generator for a radix-2 FFT Butterfly circuit *)
(****************************************************************)
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

datatype 't ParameterizedTwoInputsTrait =
  Tuple_of2p (Compute2 : "nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal") 
             (Latency2 : nat)
             (Reliability2 : real)


(******** 3.Butterfly for the FFT *********)
(******************************************)

(* datatype for modules that take w and 2 signal lists as *)
(* input, and output a signal list (type of the FFT)      *)
datatype 't ParameterizedTwoListsTrait =
  Tuple_ofL (Compute : "real \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list  \<Rightarrow> 't Signal list")
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

(* Elementary FFT (2 signals as inputs)     *)
fun fft1 :: "(nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal) \<Rightarrow>
             (nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal) \<Rightarrow> real \<Rightarrow>
             't Signal list \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list" where
   "fft1 f g w a b = ((f 0 w) (hd a, hd b)) # ((g 0 w) (hd a, hd b)) # []"

fun latency_fft1 ::
       "'t ParameterizedTwoInputsTrait \<Rightarrow> 't ParameterizedTwoInputsTrait \<Rightarrow> nat" where
   "latency_fft1 tf tg = max (Latency2 tf) (Latency2 tg)"
(* in fact lat_tf and lat_tg should be equal *)

lemma lemlatency_fft1 [simp] :
   "(Latency2 tf) = (Latency2 tg) \<Longrightarrow>
       latency_fft1 tf tg = (Latency2 tf)"
  apply (auto)
  done

(* inputs for the next upper stage      *)
fun inputs_nextstage_upper :: 
           "(nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal) 
             \<Rightarrow> ('t Signal \<times> 't Signal) list \<Rightarrow> real 
             \<Rightarrow> nat \<Rightarrow> 't Signal list" where
  "inputs_nextstage_upper foo [] w stage = []" |
  "inputs_nextstage_upper foo (x#l) w stage = 
               (foo 0 w x) # (inputs_nextstage_upper foo l w stage)"

(* inputs for the next lower stage      *)
fun inputs_nextstage_lower :: 
           "(nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal) 
             \<Rightarrow> ('t Signal \<times> 't Signal) list \<Rightarrow> real
             \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 't Signal list" where
  "inputs_nextstage_lower foo [] w stage i max_i = []" |
  "inputs_nextstage_lower foo (x#l) w stage i max_i =
            (foo (i * (power 2 (stage-1))) w x) 
            # (inputs_nextstage_lower foo l w stage (Suc i) max_i)"

(* FFT of size N        *)
fun fft :: "nat \<Rightarrow> nat 
            \<Rightarrow> (nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal)
            \<Rightarrow> (nat \<Rightarrow> real \<Rightarrow> 't Signal \<times> 't Signal \<Rightarrow> 't Signal)
            \<Rightarrow> real \<Rightarrow> 't Signal list \<Rightarrow> 't Signal list 
            \<Rightarrow> 't Signal list" where
   "fft 0 stage f g w l1 l2 = []" |
   "fft (Suc 0) stage f g w l1 l2 = []" |
   "fft (Suc (Suc 0)) stage f g w l1 l2 = (fft1 f g w l1 l2)" |
   "fft N stage f g w l1 l2 = 
                  (fft (N div 2) (Suc stage) f g w 
                       (first (inputs_nextstage_upper f (group_signal_lists l1 l2) w stage)
                              (N div 4))
                       (second (inputs_nextstage_upper f (group_signal_lists l1 l2) w stage)
                               (N div 4)))
                @ (fft (N div 2) (Suc stage) f g w 
                       (first (inputs_nextstage_lower g (group_signal_lists l1 l2) w stage
                                           0 (N div (power 2 stage)))
                              (N div 4))
                       (second (inputs_nextstage_lower g (group_signal_lists l1 l2) w stage
                                           0 (N div (power 2 stage)))
                               (N div 4)))"

fun latency_fft :: 
          "nat \<Rightarrow> 't ParameterizedTwoInputsTrait \<Rightarrow> 't ParameterizedTwoInputsTrait \<Rightarrow> nat" where
   "latency_fft 0 tf tg = 0" |
   "latency_fft (Suc 0) tf tg = 0" |
   "latency_fft (Suc (Suc 0)) tf tg = (latency_fft1 tf tg)" |
   "latency_fft N tf tg = (latency_fft (N div 2) tf tg) 
                          + (max (Latency2 tf) (Latency2 tg))"
(* in fact latencies of tf and tg should be equal *)

lemma lem1_latency_fft :
   "k \<ge> 0 \<and> (Latency2 tf) = (Latency2 tg) \<Longrightarrow>
       latency_fft (power 2 (Suc k)) tf tg = 
               latency_fft (power 2 k) tf tg + (Latency2 tf)"
   apply (induct k)
   apply (auto)
   apply (metis One_nat_def Suc_1 latency_fft.simps(3) lemlatency_fft1)
   by (smt (verit) add.commute add_cancel_left_left distrib_left_numeral latency_fft.elims latency_fft1.elims lemlatency_fft1 le_add1 mult.commute mult.left_commute mult_2 nat_less_le nonzero_mult_div_cancel_right not_less_eq numeral_1_eq_Suc_0 numeral_Bit0 plus_1_eq_Suc pos2 zero_neq_numeral)


(***** 4. Properties of the Butterfly ******)
(*******************************************)

(* Provided that f and g have the same latency l, the latency *)
(* of the Butterfly of size 2^k is k*l                         *)
lemma lemma_latency_fft :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1
                              (Compute2 (Tuple_of2p f l r1))
                              (Compute2 (Tuple_of2p g l r2)))
                         (latency_fft (power 2 k) (Tuple_of2p f l r1) (Tuple_of2p g l r2))
                         r)
       = k * l"
   apply (induct k)
   apply (auto)
  by (metis ParameterizedTwoInputsTrait.sel(2) add.commute bot_nat_0.not_eq_extremum latency_fft.simps(2) le_eq_less_or_eq lem1_latency_fft mult_is_0 nat_power_eq_Suc_0_iff power_Suc)

(* Provided that f and g have the same latency l, the latency *)
(* of the Butterfly of size 2^k equals l + the latency of the  *)
(* Butterfly of size 2^(k-1)                                   *)
lemma lemma_latency_fft_size :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1 
                              (Compute2 (Tuple_of2p f l r1))
                              (Compute2 (Tuple_of2p g l r2)))
                         (latency_fft (power 2 k) (Tuple_of2p f l r1) (Tuple_of2p g l r2))
                         r)
       = (Latency (Tuple_ofL (fft (power 2 k) 1
                                  (Compute2 (Tuple_of2p f l r1))
                                  (Compute2 (Tuple_of2p g l r2)))
                         (latency_fft (power 2 (k-1)) (Tuple_of2p f l r1) (Tuple_of2p g l r2))
                         rprime)) 
         + l"
  apply (auto)
  by (metis ParameterizedTwoInputsTrait.sel(2) Suc_leI Suc_pred add_diff_cancel_left' diff_le_mono lem1_latency_fft plus_1_eq_Suc)

(* If m>n, Latency of Butterfly with f2 and g2 of latency m =
           (Latency of Butterfly with f1 and g1 of latency n) + k*(m-n) *)
lemma lemma_latency_fft_m_n :
   "k > 0 \<and> m>n \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1 
                              (Compute2 (Tuple_of2p f2 m r12))
                              (Compute2 (Tuple_of2p g2 m r22)))
                         (latency_fft (power 2 k) (Tuple_of2p f2 m r12) (Tuple_of2p g2 m r22))
                         r)
       = (Latency (Tuple_ofL (fft (power 2 k) 1  
                                  (Compute2 (Tuple_of2p f1 n r11))
                                  (Compute2 (Tuple_of2p g1 n r21)))
                         (latency_fft (power 2 k) (Tuple_of2p f1 n r11) (Tuple_of2p g1 n r21))
                         rprime)) 
        + (k*(m-n))"
  apply (simp add: lemma_latency_fft)
  by (metis ParameterizedTwoListsTrait.sel(2) add_diff_cancel_left' distrib_left lemma_latency_fft less_imp_add_positive)


(***** 5. Instantiations for the functions for the DIF FFT *****)
(***************************************************************)

fun f_upper :: "nat \<Rightarrow> real \<Rightarrow> real Signal \<times> real Signal \<Rightarrow> real Signal" where
   "f_upper k w (x,y) = Wire ((signal_value x) + (power w k)*(signal_value y))"

fun f_lower :: "nat \<Rightarrow> real \<Rightarrow> real Signal \<times> real Signal \<Rightarrow> real Signal" where
   "f_lower k w (x,y) = Wire ((signal_value x) - (power w k)*(signal_value y))"

lemma lemma_latency_fft_inst1 :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1
                              (Compute2 (Tuple_of2p f_upper 0 r1))
                              (Compute2 (Tuple_of2p f_lower 0 r2)))
                         (latency_fft (power 2 k) (Tuple_of2p f_upper 0 r1) 
                                      (Tuple_of2p f_lower 0 r2))
                         r)
       = 0"
  using lemma_latency_fft
  by (metis mult_0_right)

lemma lemma_latency_fft_size_inst1 :
   "k > 0 \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1 
                              (Compute2 (Tuple_of2p f_upper 0 r1))
                              (Compute2 (Tuple_of2p f_lower 0 r2)))
                         (latency_fft (power 2 k) (Tuple_of2p f_upper 0 r1) 
                                      (Tuple_of2p f_lower 0 r2))
                         r)
       = (Latency (Tuple_ofL (fft (power 2 k) 1
                                  (Compute2 (Tuple_of2p f_upper 0 r1))
                                  (Compute2 (Tuple_of2p f_lower 0 r2)))
                         (latency_fft (power 2 (k-1)) (Tuple_of2p f_upper 0 r1) 
                                      (Tuple_of2p f_lower 0 r2))
                         rprime))"
  using lemma_latency_fft_size
  by (metis Nat.add_0_right)

lemma lemma_latency_fft_m_n_inst1 :
   "k > 0 \<and> m>0 \<Longrightarrow>
      Latency (Tuple_ofL (fft (power 2 k) 1 
                              (Compute2 (Tuple_of2p f_upper_v2 m r12))
                              (Compute2 (Tuple_of2p f_lower_v2 m r22)))
                         (latency_fft (power 2 k) (Tuple_of2p f_upper_v2 m r12) 
                                                  (Tuple_of2p f_lower_v2 m r22))
                         r)
       = (Latency (Tuple_ofL (fft (power 2 k) 1  
                                  (Compute2 (Tuple_of2p f_upper 0 r11))
                                  (Compute2 (Tuple_of2p f_lower 0 r21)))
                         (latency_fft (power 2 k) (Tuple_of2p f_upper 0 r11) 
                                                  (Tuple_of2p f_lower 0 r21))
                         rprime)) 
        + (k*m)"
  by (metis lemma_latency_fft mult_0_right plus_nat.add_0)

end
