import scala.math.pow
import chisel3._
import chisel3.util._
import chisel3.stage.ChiselStage


// Trait “TwoInputs”, generic model for components with two inputs of type T,
// an output of type T_out, equipped with two extra-functional properties,
// for the latency and the reliability (probability of absence of failure):

trait TwoInputs [T <: Data, T_out <: Data] {
  // expression of the functionality:
     def compute_output(x: T, y: T): T_out
  // and of extra-functional properties:
     def latency : Int
     // here we define latency as a number of clock cycles,
     // (upper bound on) the interval between valid inputs
     // and the production of valid outputs
     def reliability : Double
} 

// ======================

// Generators for concrete versions of trait TwoInputs:

// combinational adder:
class AddSimple (r:Double) extends TwoInputs[UInt,UInt] {
  override def compute_output(x:UInt, y:UInt): UInt = 
     x + y
  override def latency : Int = 0
  override def reliability : Double = r
}

// adder that buffers its output:
class AddReg (r:Double) extends TwoInputs[UInt,UInt] {
  override def compute_output(x:UInt, y:UInt): UInt = 
     RegNext(x + y)
  override def latency : Int = 1
  override def reliability : Double = r
}

// combinational multiplier:
class MulSimple (r:Double) extends TwoInputs[UInt,UInt] {
  override def compute_output(x:UInt, y:UInt): UInt = 
     x * y
  override def latency : Int = 0
  override def reliability : Double = r
}

// multiplier that buffers its output:
class MulReg (r:Double) extends TwoInputs[UInt,UInt] {
  override def compute_output(x:UInt, y:UInt): UInt = 
     RegNext(x * y)
  override def latency : Int = 1
  override def reliability : Double = r
}

// ======================

// Functions for reliability computation:
object Utils {
  // for components connected in parallel:
  def reliability_paral(R: Double, k:Int) =
       1 - pow(1-R,pow(2,k))
  // for a tree-like structure:
  def reliability_tree(R: Double, n:Int): Double=
    if (n==0) 1
    else reliability_tree(R,n-1)*reliability_paral(R,n)
}
// ("Fault-Tolerant Systems", I.Koren and C.Krishna, Morgan Kaufmann Pub., 2007)

// ======================

// Generator (concrete version of trait TwoInputs) for a dot product circuit
// with a tree-like architecture:
// (parameterized by types T1 and T2 that characterize the multiplication
// and addition subcomponents; they must be subtypes of trait TwoInputs)

class ParameterizedDotProduct
    [T1 <: TwoInputs[UInt,UInt], T2 <: TwoInputs[UInt,UInt]](
  val width: Int, 
  val nElem: Int,
  val relreg: Double,
  mulFunc: => T1, 
  addFunc: => T2
) extends Module with TwoInputs[Vec[UInt],UInt]{
  require(nElem > 0, "nElem should at least be 1")
  require(width > 0, "width should at least be 1")

  val tpe = UInt(width.W)
  val io  = IO(new Bundle {       // I/O ports
    val vec1 = Input(Vec(nElem, tpe))
    val vec2 = Input(Vec(nElem, tpe))
    val out  = Output(UInt())
  })

  def compute_output (v1: Vec[UInt],v2: Vec[UInt]) =
    VecInit(((v1 zip v2).
     map{case(a,b) => mulFunc.compute_output(a,b)})).
     reduceTree(addFunc.compute_output(_,_))

  def corelatency = mulFunc.latency 
               + log2Ceil(nElem)*(addFunc.latency) 
  def latency = corelatency + 2

  def reliability = 
      Utils.reliability_paral(relreg,log2Ceil(nElem)+1) *
      Utils.reliability_paral(mulFunc.reliability,log2Ceil(nElem)) *
      Utils.reliability_tree(addFunc.reliability,log2Ceil(nElem)-1) *
      relreg

  // buffer input ports in registers
  val vec1Buffered = RegNext(io.vec1)
  val vec2Buffered = RegNext(io.vec2)

  // outBuffer is the result of the dot product:
  val outBuffer = Reg(UInt())
  outBuffer := compute_output(vec1Buffered,vec2Buffered)
  io.out := outBuffer
}
