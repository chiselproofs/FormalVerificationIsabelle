import scala.math.pow
import chisel3._
import chisel3.util._
import chisel3.experimental.FixedPoint
import chisel3.stage.ChiselStage

////////////////////////////////////////////////////////////
// This file contains:
// - a generic trait for components with two (scalar) inputs
// - a generic trait for components with two vectorial inputs
// - and a generator for a specialized form of butterfly component
// for a radix-2 DIF FFT
///////////////////////////////////////////////////////////
// Author L.Pierre


// Trait “ParameterizedTwoInputs”, generic model for components 
// with two inputs of type T
// (parameters k and w of function compute_output will be used
// for the computation of the twiddle factors)

// Trait for the modules in the butterfly:
trait ParameterizedTwoInputs [T <: Data] {
  // expression of the functionality:
     def compute_output(k: Int)(w: Double)(x: T, y: T): T
  // and of extra-functional properties:
     def latency : Int
     // here we define latency as a number of clock cycles,
     // (upper bound on) the interval between valid inputs
     // and the production of valid outputs
     def reliability : Double
} 

// ======================

// Generators for concrete versions of trait ParameterizedTwoInputs,
// subcomponents in the upper butterfly for each next stage and 
// in the lower butterfly for each next stage:

class f1 (width: Int, pos: Int, r:Double) 
      extends ParameterizedTwoInputs[FixedPoint] {
  override def compute_output(k: Int)(w: Double)(x:FixedPoint, y:FixedPoint): FixedPoint = 
     x + (y * FixedPoint.fromDouble(math.pow(w, k), width.W, pos.BP))
  override def latency : Int = 0
  override def reliability : Double = r
}

class f2 (width: Int, pos: Int, r:Double) 
      extends ParameterizedTwoInputs[FixedPoint] {
  override def compute_output(k: Int)(w: Double)(x:FixedPoint, y:FixedPoint): FixedPoint = 
     x - (y * FixedPoint.fromDouble(math.pow(w, k), width.W, pos.BP))
  override def latency : Int = 0
  override def reliability : Double = r
}

// ======================

// Trait “ParameterizedTwoInputLists”, generic model for components 
// with two vectorial inputs of type T

trait ParameterizedTwoInputLists [T <: Data] {
  // expression of the functionality:
     def compute_output(w:Double)(x: Vec[T], y: Vec[T]): Vec[T]
  // and of extra-functional properties:
     def latency : Int
     // here we define latency as a number of clock cycles,
     // (upper bound on) the interval between valid inputs
     // and the production of valid outputs
     def reliability : Double
} 

// ======================

// Generator (concrete version of trait ParameterizedTwoInputLists) for 
// a radix-2 DIF FFT circuit.
// Subcomponents in the upper butterfly for the next stage and in the 
// lower butterfly for the next stage must be respectively of types T1 
// and T2 (which must be subtypes of trait ParameterizedTwoInputs)

// FFT of size N
class FFT [T1 <: ParameterizedTwoInputs[FixedPoint],
           T2 <: ParameterizedTwoInputs[FixedPoint]](
  val N: Int,
  val width: Int, 
  val pos: Int, 
  val w: Double,
  val rel: Double,
  f: => T1, 
  g: => T2
) extends Module with ParameterizedTwoInputLists[FixedPoint]{
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

  // FFT of size 2 (2 signals as inputs)     
  def create_FFT1[T](x: Seq[T], y: Seq[T], w: Double,
                     f: Int => Double => (T, T) => T, 
                     g: Int => Double => (T, T) => T) : Seq[T] = 
    Seq((f(0)(w))(x(0),y(0)), (g(0)(w))(x(0),y(0)))

  def computelatency_fft1 : Int = 
    (f.latency).max(g.latency)

  // Inputs for the next upper stage
  def inputs_nextstage_upper[T](foo: Int => Double => (T, T) => T,
                                 x: Seq[(T,T)], w: Double, stage: Int) : Seq[T] =
    if (x.isEmpty)
    Seq()
    else (foo(0)(w)).tupled(x(0)) +: inputs_nextstage_upper(foo,x.tail,w,stage)

  // Inputs for the next lower stage
  def inputs_nextstage_lower[T](foo: Int => Double => (T, T) => T,
                                 x: Seq[(T,T)], w: Double, stage: Int, 
                                 i: Int, max_i: Int) : Seq[T] =
    if (x.isEmpty)
    Seq()
    else (foo(i * (math.pow(2, stage-1)).toInt)(w)).tupled(x(0)) +: 
         inputs_nextstage_lower(foo,x.tail,w,stage,i+1,max_i)

  def create_FFT[T](N: Int, stage: Int, x: Seq[T], y: Seq[T], w: Double,
                    f: Int => Double => (T, T) => T, 
                    g: Int => Double => (T, T) => T) : Seq[T] = 
    N match {
        case 0 => Seq()
        case 1 => Seq()
        case 2 => create_FFT1(x,y,w,f,g)
        case _ => 
          (create_FFT(N/2, stage+1, 
                    first(inputs_nextstage_upper(f,group_signal_lists(x,y),w,stage), N/4),
                    second(inputs_nextstage_upper(f,group_signal_lists(x,y),w,stage), N/4),
                    w,f,g)) ++ 
          (create_FFT(N/2, stage+1,
                    first(inputs_nextstage_lower(g,group_signal_lists(x,y),
                                                 w,stage,0,N/(math.pow(2,stage)).toInt), N/4),
                    second(inputs_nextstage_lower(g,group_signal_lists(x,y),
                                                 w,stage,0,N/(math.pow(2,stage)).toInt), N/4),
                    w,f,g))
    }

   def computelatency_fft(N: Int): Int = 
    N match {
        case 0 => 0
        case 1 => 0
        case 2 => computelatency_fft1
        case _ => computelatency_fft(N/2) + (f.latency).max(g.latency)
    }

  def compute_output (w:Double)(x:Vec[FixedPoint], y:Vec[FixedPoint]) =
    VecInit(create_FFT(N,1,x,y,w,f.compute_output,g.compute_output))

  def latency = computelatency_fft(N)

  def reliability = rel  // not yet considered

  io.out := compute_output(w)(io.a,io.b)
}
