import scala.math.pow
import chisel3._
import chisel3.util._
import chisel3.experimental.FixedPoint
import chisel3.stage.ChiselStage

////////////////////////////////////////////////////////////
// This file contains:
// - a generic trait for components with two (scalar) inputs
// (the same as the one for tree-like structure)
// - a generic trait for components with two vectorial inputs
// - and a generator for a general form of butterfly component
///////////////////////////////////////////////////////////
// Author L.Pierre



// Trait “TwoInputs”, generic model for components with two inputs of type T,
// an output of type T_out

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

class f_plus (r:Double) extends TwoInputs[FixedPoint,FixedPoint] {
  override def compute_output(x:FixedPoint, y:FixedPoint): FixedPoint = 
     x + y
  override def latency : Int = 0
  override def reliability : Double = r
}

class f_minus (r:Double) extends TwoInputs[FixedPoint,FixedPoint] {
  override def compute_output(x:FixedPoint, y:FixedPoint): FixedPoint = 
     x - y
  override def latency : Int = 0
  override def reliability : Double = r
}

// ======================

// Trait “TwoInputLists”, generic model for components with two vectorial
// inputs of type T

trait TwoInputLists [T <: Data] {
  // expression of the functionality:
     def compute_output(x: Vec[T], y: Vec[T]): Vec[T]
  // and of extra-functional properties:
     def latency : Int
     // here we define latency as a number of clock cycles,
     // (upper bound on) the interval between valid inputs
     // and the production of valid outputs
     def reliability : Double
} 

// ======================

// Generator (concrete version of trait TwoInputLists) for a general form
// of BUTTERFLY circuit: subcomponents in the upper butterfly for the next 
// stage and in the lower butterfly for the next stage must be respectively
// of types T1 and T2 (which must be subtypes of trait TwoInputs)

// Butterfly of size N
class Butterfly [T1 <: TwoInputs[FixedPoint,FixedPoint],
                 T2 <: TwoInputs[FixedPoint,FixedPoint]](
  val N: Int,
  val width: Int, 
  val pos: Int, 
  val rel: Double,
  f: => T1, 
  g: => T2
) extends Module with TwoInputLists[FixedPoint]{
  require(width > 0, "width should at least be 1")
  require((N & (N-1)) == 0 && N > 1, "N should be a power of 2")
  
  val tpe = FixedPoint(width.W,pos.BP)
  val io  = IO(new Bundle {       // I/O ports
    val a = Input(Vec(N/2, tpe))
    val b = Input(Vec(N/2, tpe))
    val out  = Output(Vec(N, tpe))
  })

  // To group the elements of two lists 2 by 2
  def group_signal_lists[T](x: Seq[T], y: Seq[T]) : Seq[(T,T)] =
    if (x.isEmpty || y.isEmpty)
    Seq()
    else (x(0),y(0)) +: group_signal_lists(x.tail,y.tail)

  // To split a list into 2 parts of identical lengths:
  def first[T](x: Seq[T], n : Int) : Seq[T] =
    if (x.isEmpty || n==0)
    Seq()
    else x(0) +: first(x.tail,n-1)

  def second[T](x: Seq[T], n : Int) : Seq[T] =
    if (n==0)
    x
    else second(x.tail,n-1)

  // Butterfly of size 2 (2 signals as inputs)     
  def create_butterfly1[T](x: Seq[T], y: Seq[T], f: (T, T) => T, g: (T, T) => T) : Seq[T] = 
    Seq(f(x(0),y(0)), g(x(0),y(0)))

  def computelatency_butterfly1 : Int = 
    (f.latency).max(g.latency)

  def create_butterfly[T](N: Int, x: Seq[T], y: Seq[T], f: (T, T) => T, g: (T, T) => T) : Seq[T] = 
    N match {
        case 0 => Seq()
        case 1 => Seq()
        case 2 => create_butterfly1(x,y,f,g)
        case _ => 
          (create_butterfly(N/2, 
                    first(group_signal_lists(x,y).map{case(a,b) => f(a,b)}, N/4),
                    second(group_signal_lists(x,y).map{case(a,b) => f(a,b)}, N/4),
                    f,g)) ++ 
          (create_butterfly(N/2, 
                    first(group_signal_lists(x,y).map{case(a,b) => g(a,b)}, N/4),
                    second(group_signal_lists(x,y).map{case(a,b) => g(a,b)}, N/4),
                    f,g))
    }

   def computelatency_butterfly(N: Int): Int = 
    N match {
        case 0 => 0
        case 1 => 0
        case 2 => computelatency_butterfly1
        case _ => computelatency_butterfly(N/2) + (f.latency).max(g.latency)
    }

  def compute_output (x:Vec[FixedPoint], y:Vec[FixedPoint]) =
    VecInit(create_butterfly(N,x,y,f.compute_output,g.compute_output))

  def latency = computelatency_butterfly(N)

  def reliability = rel  // not yet considered

  io.out := compute_output(io.a,io.b)
}
