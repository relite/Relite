/*
 * Copyright (c) 2013 Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/agpl.html.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package relite

import r._
import r.data._
import r.data.internal._
import r.builtins.{ CallFactory, Primitives }
import r.nodes._
import r.nodes.truffle.{ BaseR, RNode }
import com.oracle.truffle.api.frame._;

import org.antlr.runtime._

import java.io._

import scala.collection.JavaConversions._
import optiml.shared.{ OptiMLApplication }
import ppl.delite.framework.transform._
import scala.virtualization.lms.common.StaticData
import ppl.delite.framework.datastructures.DeliteArray
import optiml.compiler.ops._
import ppl.delite.framework.datastructures._
import optiml.compiler.OptiMLApplicationCompiler
import scala.collection.mutable

trait Eval extends OptiMLApplicationCompiler with StaticData {
  type Env = mutable.Map[RSymbol, Rep[Any]]
  var env: Env = mutable.Map.empty

  //storing declared functions
  type EnvFunct = Map[RSymbol, Function]
  var envFunctions: EnvFunct = Map.empty

  var globalEnv: scala.collection.immutable.Map[RSymbol, Rep[Any]] = scala.collection.immutable.Map.empty

  def infix_tpe[T](x: Rep[T]): Manifest[_]

  //def fun[A,B](f: Rep[A]=>Rep[B]):Rep[A=>B]
  def nuf[A, B](f: Rep[A => B]): Rep[A] => Rep[B]

  def liftValue(v: Any): Rep[Any] = v match {
    case v: RString => unit(v.getString(0))
    case v: ScalarIntImpl => unit(v.getInt(0))
    case v: ScalarDoubleImpl => unit(v.getDouble(0))
    case v: IntImpl =>
      val data = staticData(v.getContent).as[DeliteArray[Int]]
      densevector_fromarray(data, true)
    case v: DoubleImpl =>
      val data = staticData(v.getContent).as[DeliteArray[Double]]
      densevector_fromarray(data, true)
    //representing boolean
    case v: RLogical =>
      val intLogicalVal = v.getLogical(0)
      if (intLogicalVal == 1) unit(true) else unit(false)
  }

  def convertBack(x: Any): AnyRef = x match {
    case x: String => RString.RStringFactory.getScalar(x)
    case x: Int => RInt.RIntFactory.getScalar(x)
    case x: Double => RDouble.RDoubleFactory.getScalar(x)
    // struct classes are generated on the fly. we cannot acces them yet.
    case x if x.getClass.getName == "generated.scala.DenseVectorInt" => RInt.RIntFactory.getFor(x.asInstanceOf[{ val _data: Array[Int] }]._data)
    case x if x.getClass.getName == "generated.scala.DenseVectorDouble" => RDouble.RDoubleFactory.getFor(x.asInstanceOf[{ val _data: Array[Double] }]._data)
    //    case x: generated.scala.DenseVectorDouble => RDouble.RDoubleFactory.getFor(x._data)
    case () => RInt.RIntFactory.getScalar(0)
  }

  def evalFun[A: Manifest, B: Manifest](e: ASTNode, frame: Frame): Rep[A] => Rep[B] = e match {
    case e: Function =>
      {
        x: Rep[A] =>
          val ex = RContext.createRootNode(e, null).execute(frame)
          ex match {
            case ex: ClosureImpl =>
              val env0 = env
              // TODO: closure env?
              env = env.updated(ex.function.paramNames()(0), x)
              val res = eval(ex.function.body.getAST, ex.enclosingFrame)
              env = env0
              res.as[B]
          }
      }
  }

  //casting function
  implicit class Cast(x: Rep[Any]) { def as[T]: Rep[T] = x.asInstanceOf[Rep[T]] }

  def eval(e: ASTNode, frame: Frame): Rep[Any] = e match {
    case e: r.nodes.Constant => liftValue(e.getValue())
    case e: SimpleAssignVariable =>
      val lhs = e.getSymbol
      val rhs = e.getExpr
      rhs match {
        case rhs: Function =>
          envFunctions = envFunctions.updated(lhs, rhs)
        case _ =>
          val rhss = eval(rhs, frame)
          env = env.updated(lhs, rhss)
      }
    case e: SimpleAccessVariable =>
      val lhs = e.getSymbol
      env.getOrElse(lhs, {
        val ex = RContext.createRootNode(e, null).execute(frame)
        liftValue(ex)
      })
    case e: Sequence =>
      e.getExprs.map(g => eval(g, frame)).last
    case e: Add =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) => lhs.as[Double] + rhs.as[Double]
        case (VD, VD) => lhs.as[DenseVector[Double]] + rhs.as[DenseVector[Double]]
        case (VD, D) => lhs.as[DenseVector[Double]] + rhs.as[Double]
        case (VM, VM) => lhs.as[DenseMatrix[Double]] + rhs.as[DenseMatrix[Double]]
      }
    case e: Mult =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) => lhs.as[Double] * rhs.as[Double]
        case (VD, VD) =>
          val lhs1 = lhs.as[DenseVector[Double]]
          val rhs1 = rhs.as[DenseVector[Double]]
          val res = lhs1.Clone * rhs1.Clone
          res.as[DenseVector[Double]]
        case (VD, D) => lhs.as[DenseVector[Double]] * rhs.as[Double]
        case (VM, VM) =>
          val m1 = rhs.as[DenseMatrix[Double]]
          val m2 = lhs.as[DenseMatrix[Double]]
          val res = m1 *:* m2
          res.as[DenseMatrix[Double]]
        case (VD, VM) =>
          val vector = lhs.as[DenseVector[Double]]
          val matrix = rhs.as[DenseMatrix[Double]]
          val vectorSize = vector.length
          val matrixRows = matrix.numRows
          val matrixCols = matrix.numCols
          val res = matrix.mutable
          var i = 0
          while (i < matrixRows) {
            var j = 0
            while (j < matrixCols) {
              res(i, j) = res(i, j) * vector(i % vectorSize)
              j += 1
            }
            i += 1
          }
          res
        case (D, VD) => rhs.as[DenseVector[Double]] * lhs.as[Double]
      }

    case e: Div =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) => lhs.as[Double] / rhs.as[Double]
        case (VD, VD) => lhs.as[DenseVector[Double]] / rhs.as[DenseVector[Double]]
        case (VD, D) => lhs.as[DenseVector[Double]] / rhs.as[DenseVector[Double]]
        case (D, VM) =>
          val matrix = rhs.as[DenseMatrix[Double]]
          val num = lhs.as[Double]
          matrix.map(a => num / a)
        case (VM, D) =>
          val matrix = lhs.as[DenseMatrix[Double]]
          val num = rhs.as[Double]
          val res = matrix.map(a => a / num)
          res.as[DenseMatrix[Double]]
        case (VM, VM) =>
          val m1 = lhs.as[DenseMatrix[Double]]
          val m2 = rhs.as[DenseMatrix[Double]]
          val res = m1 / m2
          res.as[DenseMatrix[Double]]
      }

    //subtraction
    case e: Sub =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) =>
          val v1 = lhs.as[Double]
          val v2 = rhs.as[Double]
          (v1 - v2).as[Double]
        case (VD, VD) =>
          val v1 = lhs.as[DenseVector[Double]]
          val v2 = rhs.as[DenseVector[Double]]
          (v1 - v2).as[DenseVector[Double]]
      }

    /* case e: Colon =>
      val lhs: Rep[Any] = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) =>
          DenseVector.range(
            lhs.as[Double].toInt,
            rhs.as[Double].toInt + 1).toDouble
      }
*/
    case e: FunctionCall =>
      e.getName.toString match {
        case "map" | "sapply" =>
          val v = (eval(e.getArgs.getNode(0), frame)).as[DenseVector[Double]]
          val f = evalFun[Double, Double](e.getArgs.getNode(1), frame)
          v.map(f)
        case "sum" =>
          val v = (eval(e.getArgs.getNode(0), frame)).as[DenseVector[Double]]
          v.sum

        //Vector creation
        case "c" =>
          val first = eval(e.getArgs.getNode(0), frame)
          val sizeVect: Int = e.getArgs.size()
          val v1 = DenseVector[Double](e.getArgs.size(), true)

          for ((i: Int) <- (0 to (sizeVect - 1))) {
            v1(i) = (eval(e.getArgs.getNode(i), frame)).as[Double]
          }
          v1

        //function as.vector
        case "as.vector" =>
          val myArg = eval(e.getArgs.getNode(0), frame)
          if (myArg.isInstanceOf[Rep[DenseVector[Double]]])
            myArg.as[DenseVector[Double]]
          else if (myArg.isInstanceOf[Rep[DenseMatrix[Double]]]) {
            val matrix = myArg.as[DenseMatrix[Double]]
            val vectSize = matrix.numRows * matrix.numCols
            val res = DenseVector[Double](vectSize, true)
            var ii = 0
            while (ii < matrix.numRows) {
              var jj = 0
              while (jj < matrix.numCols) {
                res(matrix.numCols * ii + jj) = matrix(ii, jj)
                jj += 1
              }
              ii += 1
            }
            res
          } else
            unit(())

        //function sqrt, for numbers and matrice
        case "sqrt" =>
          val arg = eval(e.getArgs.getNode(0), frame)
          val VD = manifest[DenseMatrix[Double]]
          val D = manifest[Double]
          arg.tpe match {
            case D =>
              val num = arg.as[Double]
              sqrt(num)
            case VD =>
              val matrix = arg.as[DenseMatrix[Double]]
              matrix.map(a => sqrt(a))
          }

        //function upper.tri
        case "upper.tri" =>
          val matrix = (eval(e.getArgs.getNode(0), frame)).as[DenseMatrix[Double]]
          val resMatr = DenseMatrix[Boolean](matrix.numRows, matrix.numCols)
          var i = 0
          while (i < matrix.numRows) {
            var j = 0
            while (j < matrix.numCols) {
              if (i < j)
                resMatr(i, j) = true
              else
                resMatr(i, j) = false
              j += 1
            }
            i += 1
          }
          resMatr.as[DenseMatrix[Boolean]]

        //function cat
        case "cat" =>
          val args: List[Any] = e.getArgs.map(g => eval(g.getValue, frame)).toList
          for (arg <- args) {
            ???
          }

        //function diag
        case "diag" =>
          val matrix = (eval(e.getArgs.getNode(0), frame)).as[DenseMatrix[Double]]
          val diagonal = DenseVector[Double](matrix.numRows, true)
          var i = 0
          while (i < matrix.numRows) {
            diagonal(i) = matrix(i, i)
            i += 1
          }
          diagonal

        //function diag for assigment
        case "diag<-" =>
          val matrix = (eval(e.getArgs.getNode(0), frame)).as[DenseMatrix[Double]]
          val number = (eval(e.getArgs.getNode(1), frame)).as[Double]

          val invertEnv = env.map(_.swap)
          val theKey: RSymbol = invertEnv(matrix)
          val matrMut = (matrix.mutable).as[DenseMatrix[Double]]

          var i = 0
          while (i < matrMut.numRows) {
            matrMut(i, i) = number
            i += 1
          }
          env = env.updated(theKey, (matrMut.Clone).as[DenseMatrix[Double]])
          unit(())

        //return
        //TODO: handle cases when return is in the middle of function body
        case "return" =>
          val value = eval(e.getArgs.getNode(0), frame)
          val D = manifest[Double]
          val I = manifest[Int]
          (value.tpe) match {
            case D => value.as[Double]
            case I => value.as[Int]
            case _ => value
          }

        case "as.integer" =>
          val arg = eval(e.getArgs.getNode(0), frame)
          val D = manifest[Double]
          (arg.tpe) match {
            case D => ((arg.as[Double]).toInt).as[Int]
          }

        //function uoter
        case "outer" =>
          val args = e.getArgs
          val v1 = (eval(args.getNode(0), frame)).as[DenseVector[Double]]
          val v2 = (eval(args.getNode(1), frame)).as[DenseVector[Double]]
          val op = eval(args.getNode(2), frame)
          val VD = manifest[DenseVector[Double]]
          (v1.tpe, v2.tpe) match {
            case (VD, VD) =>
              if (op == "-") {
                val res = DenseMatrix[Double](v1.length, v2.length)
                var i = 0
                while (i < v1.length) {
                  var j = 0
                  while (j < v2.length) {
                    res(i, j) = (v1(i) - v2(j)).as[Double]
                    j += 1
                  }
                  i += 1
                }
                res
              } else { //the default case
                val res = DenseMatrix[Double](v1.length, v2.length)
                var i = 0
                while (i < v1.length) {
                  var j = 0
                  while (j < v2.length) {
                    res(i, j) = (v1(i) * v2(j)).as[Double]
                    j += 1
                  }
                  i += 1
                }
                res
              }
          }

        //function exists
        case "exists" =>
          val name: String = e.getArgs.getNode(0).toString //name of the value, we are searching for, string
          val keys = env.keySet
          var isPresent: Rep[Boolean] = unit(false)
          for ((k: RSymbol) <- keys) {
            if (k.name.toString.equals(name)) isPresent = unit(true)
          }
          isPresent

        //function length
        case "length" =>
          val VD = manifest[DenseVector[Double]]
          val D = manifest[Double]
          val arg = eval(e.getArgs.getNode(0), frame)
          (arg.tpe) match {
            case VD => ((arg.as[DenseVector[Double]]).length).as[Int]
            case D =>
              val value = arg.as[Double]
              ((value / value).toInt).as[Int]
            case _ =>
              val value = arg.as[Double]
              ((value - value).toInt).as[Int]
          }

        //function options
        //TODO: fix/complete it. This doesn't work for now
        case "options" =>
          val arg = e.getArgs.getNode(0)
          val I = manifest[Int]
          (arg) match {
            case arg: Constant =>
              val const = eval(arg, frame)
            //    (const.tpe) match{
            //      case I=>digits=const.toInt //here digits should be some global value
            //      unit(())
            //    }
          }

        //function rep
        case "rep" =>
          val args = e.getArgs
          val num = eval(args.getNode(0), frame)
          val times = eval(args.getNode(1), frame)
          val D = manifest[Double]
          (num.tpe, times.tpe) match {
            case (D, D) =>
              val number = num.as[Double]
              val t = ((times.as[Double]).toInt).as[Int]
              val resultingVector = DenseVector.zeros(t).map(e => number)
              resultingVector
          }

        //function seq
        case "seq" =>
          val arg = eval(e.getArgs.getNode(0), frame)
          val D = manifest[Double]
          (arg.tpe) match {
            case D =>
              val arg1 = arg.as[Double]
              DenseVector.uniform(1, 1, arg1 + 1)
          }

        case "double" =>
          println("poziv funkcije double")
          val num = eval(e.getArgs.getNode(0), frame)
          val D = manifest[Double]
          num.tpe match {
            case D =>
              val number = ((num.as[Double]).toInt).as[Int]
              val resultingVector = DenseVector.zeros(number)
              resultingVector.pprint
              resultingVector
          }

        case "mean" =>
          val v = (eval(e.getArgs.getNode(0), frame)).as[DenseVector[Double]]
          (sum(v) / v.length).as[Double]

        case "print" =>
          val arg = e.getArgs
          val VD = manifest[DenseVector[Double]]
          for ((i: Int) <- (0 to arg.size - 1)) {
            val a = eval(arg.getNode(i), frame)
            a.tpe match {
              case VD => (a.as[DenseVector[Double]]).pprint
              case _ => println(a)
            }
          }

        //calls of defined functions
        //not working for arguments with default values yet
        case _ =>
          val keys = envFunctions.keySet
          val callName = e.getName.toString
          if (keys.contains(e.getName)) {
            val functionNode = envFunctions(e.getName)
            val signature = functionNode.getSignature
            val arguments = e.getArgs

            val currentEnv = env.clone

            val realNrArgs = arguments.size
            val expectedNrArgs = signature.size
            if (realNrArgs == expectedNrArgs) {
              val argNames = signature.map(g => g.getName).toList
              for ((i: Int) <- (0 to realNrArgs - 1)) {
                env = env.updated(argNames(i), eval(arguments.getNode(i), frame))
              }
              val result = eval(functionNode.getBody, frame)
              globalEnv.foreach((pair: Tuple2[RSymbol, Rep[Any]]) => currentEnv.update(pair._1, pair._2))
              env = currentEnv
              globalEnv = scala.collection.immutable.Map.empty

              val VD = manifest[DenseVector[Double]]
              val D = manifest[Double]

              (result.tpe) match {
                case VD =>
                  println("Function return type - Rep[DenseVector[Double]]") // TODO: remove this; debugging purpose
                  result.as[DenseVector[Double]]
                case D =>
                  println("Function return type - Rep[Double]") //TODO: remove this
                  result.as[Double]
                case _ => //TODO: expand for other cases, for now, double is enough
                  println("Function return type - Something else") //TODO: remove this
                  result
              }
            } else {
              println("Error in function call")
            }
          } else {
            val args = e.getArgs.map(g => eval(g.getValue, frame)).toList
            (e.getName.toString, args) match {
              case ("Vector.rand", (n: Rep[Double]) :: Nil) =>
                assert(n.tpe == manifest[Double])
                DenseVector.rand(n.toInt)
              case s => println("unknown f: " + s + " / " + args.mkString(","));
            }
          }
      }

    //vectors outer product, just for vectors of double for now
    case e: OuterMult =>
      val firstVect = eval(e.getLHS, frame)
      val secondVect = eval(e.getRHS, frame)
      val VD = manifest[DenseVector[Double]]
      (firstVect.tpe, secondVect.tpe) match {
        case (VD, VD) =>
          val first = firstVect.as[DenseVector[Double]]
          val second = secondVect.as[DenseVector[Double]]
          val res = first ** second
          res.as[DenseMatrix[Double]]
      }

    //matrix multiplication, just for double for now
    case e: MatMult =>
      val matr1 = eval(e.getLHS, frame)
      val matr2 = eval(e.getRHS, frame)
      val VM = manifest[DenseMatrix[Double]]
      val VD = manifest[DenseVector[Double]]
      (matr1.tpe, matr2.tpe) match {
        case (VM, VM) =>
          (matr1.as[DenseMatrix[Double]] *:* matr2.as[DenseMatrix[Double]]).as[DenseMatrix[Double]]
        case (VM, VD) =>
          val vect = matr2.as[DenseVector[Double]]
          val matr = matr1.as[DenseMatrix[Double]]
          (matr.mapRowsToVector(row => sum(row * vect))).as[DenseMatrix[Double]]
      }

    //just for single double for now
    case e: UnaryMinus =>
      val lhs = eval(e.getLHS, frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      lhs.tpe match {
        case D => (-1 * lhs.as[Double])
      }

    //if node - with or without else
    case e: If =>
      val cond = eval(e.getCond, frame)
      val trueCase = eval(e.getTrueCase, frame)
      val falseCase = eval(e.getFalseCase, frame)
      val D = manifest[Double]
      val B = manifest[Boolean]
      val I = manifest[Int]
      cond.tpe match {
        case B =>
          val condition = cond.as[Boolean]
          (trueCase.tpe, falseCase.tpe) match {
            case (D, D) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (I, I) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (I, D) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (D, I) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (_, _) =>
              if (condition) trueCase.as[AnyVal] else falseCase.as[AnyVal]
          }
        case I =>
          val condition = (cond.as[Int] != 0).as[Boolean]
          (trueCase.tpe, falseCase.tpe) match {
            case (D, D) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (I, I) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (I, D) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (D, I) =>
              if (condition) trueCase.as[Double] else falseCase.as[Double]
            case (_, _) =>
              if (condition) trueCase.as[AnyVal] else falseCase.as[AnyVal]
          }
      }

    //access double value vector node
    case e: AccessVector =>
      val vect = eval(e.getVector, frame)
      val arg = eval(e.getArgs.getNode(0), frame)
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      val D = manifest[Double]
      val BM = manifest[DenseMatrix[Boolean]]
      (vect.tpe) match {
        case VD =>
          (arg.tpe) match {
            case D =>
              val ind: Rep[Int] = arg.as[Int]
              val vector = vect.as[DenseVector[Double]]
              val res = vector(ind.toInt - 1)
              res.as[Double]
          }
        case D => vect.as[Double]
        case VM =>
          (arg.tpe) match {
            case BM =>
              val matrix = vect.as[DenseMatrix[Double]]
              val upperTriMatr = arg.as[DenseMatrix[Boolean]]
              val rows = matrix.numRows
              val cols = matrix.numCols
              val dim = rows * cols
              val resultVect = DenseVector[Double](dim, true)
              var i = 0
              var count = 0
              while (i < dim) {
                if (upperTriMatr(i % cols, i / cols)) {
                  resultVect(count) = matrix(i % cols, i / cols)
                  count += 1
                }
                i += 1
              }
              (resultVect.take(count)).as[DenseVector[Double]]
          }
      }

    //update double value vector node
    case e: UpdateVector =>
      val rhs = (eval(e.getRHS, frame)).as[Double]
      val accessVector = e.getVector
      val vect = (eval(accessVector.getVector, frame)).as[DenseVector[Double]]
      val arg = (eval(accessVector.getArgs.getNode(0), frame)).as[Int]
      val index = (arg.toInt - 1).toInt

      val invertEnv = env.map(_.swap)
      val theKey: RSymbol = invertEnv(vect)

      val vectMut = DenseVector[Double](vect.length, true)
      var i = 0
      while (i < index) {
        vectMut(i) = vect(i)
        i += 1
      }
      vectMut(index) = rhs
      i += 1
      while (i < vect.length) {
        vectMut(i) = vect(i)
        i += 1
      }
      if (e.isSuper())
        globalEnv = globalEnv.updated(theKey, vectMut)
      else
        env = env.updated(theKey, vectMut.Clone)

    //for loop
    case e: For =>
      val body: ASTNode = e.getBody
      val envBeforeLoop = env.clone
      val counter: RSymbol = e.getCVar
      val range: Rep[DenseVector[Double]] = (eval((e.getRange: ASTNode), frame)).as[DenseVector[Double]]
      val bodyEvaluated: Rep[Any] = unit(())
      range.foreach { (currVal: Rep[Double]) =>
        env = env.updated(counter, currVal)
        bodyEvaluated = eval(body, frame)
      }
      env = envBeforeLoop
      bodyEvaluated

    //not node-just for single boolean, for now
    case e: Not =>
      val lhs = eval(e.getLHS, frame)
      val B = manifest[Boolean]
      lhs.tpe match {
        case B => !lhs.as[Boolean]
      }

    //elementwise and - just for simple boolean values, not vectors, for now
    case e: ElementwiseAnd =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val B = manifest[Boolean]
      (lhs.tpe, rhs.tpe) match {
        case (B, B) =>
          (lhs.as[Boolean] && rhs.as[Boolean]).as[Boolean]
      }

    //elementwise or - just for simple boolean values, not vectors, for now
    case e: ElementwiseOr =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val B = manifest[Boolean]
      (lhs.tpe, rhs.tpe) match {
        case (B, B) => lhs.as[Boolean] || rhs.as[Boolean]
      }

    //integer division - just for simple values for now
    case e: IntegerDiv =>
      val lhs = eval(e.getLHS, frame)
      val rhs = eval(e.getRHS, frame)
      val D = manifest[Double]
      (lhs.tpe, rhs.tpe) match {
        case (D, D) => (lhs.as[Double] / (rhs.as[Double]).toInt).as[Int]
      }

    case _ =>
      println("unknown: " + e + "/" + e.getClass);
      new RLanguage(e) //RInt.RIntFactory.getScalar(42)
      42
  }
}

class EvalRunner extends MainDeliteRunner with Eval { self =>

  def nuf[A, B](f: Rep[A => B]): Rep[A] => Rep[B] = f match { case Def(Lambda(f, _, _)) => f }

  def infix_tpe[T](x: Rep[T]): Manifest[_] = x.tp

  val transport: Array[Any] = new Array[Any](1)
  def setResult(x: Rep[Any]): Rep[Any] =
    darray_update(staticData(transport).as[ForgeArray[Any]], 0, x)

  def getResult: AnyRef = convertBack(transport(0))
}

object DeliteBridge {

  def install(): Unit = {
    installDelite()
    installTime()
  }

  // todo: Delitec(function (x) { })

  def installDelite(): Unit = {
    val cf = new CallFactory("Delite", Array("e"), Array("e")) {
      def create(call: ASTNode, names: Array[RSymbol], exprs: Array[RNode]): RNode = {
        check(call, names, exprs)
        val expr = exprs(0)
        val ast = expr.getAST()
        val ast1: AnyRef = ast // apparently ASTNode member fields are reassigned -- don't make it look like one!
        new BaseR(call) {
          def execute(frame: Frame): AnyRef = {
            val ast = ast1.asInstanceOf[ASTNode]
            println("delite input: " + ast)

            val runner = new EvalRunner {}
            runner.program = { x =>
              val res = runner.eval(ast, null)
              runner.setResult(res)
            }
            DeliteRunner.compileAndTest(runner)
            runner.getResult
          }
        }
      }
    }

    Primitives.add(cf)
  }
  def installTime(): Unit = {
    val cf = new CallFactory("system.time", Array("e"), Array("e")) {
      def create(call: ASTNode, names: Array[RSymbol], exprs: Array[RNode]): RNode = {
        check(call, names, exprs)
        val expr = exprs(0)
        //val ast = expr.getAST()

        //val ast1:AnyRef = ast // apparently ASTNode member fields are reassigned -- don't make it look like one!
        new BaseR(call) {
          def execute(frame: Frame): AnyRef = {
            val t0 = System.currentTimeMillis()
            val res = expr.execute(frame)
            val t1 = System.currentTimeMillis()
            println("elapsed: " + ((t1 - t0) / 1000.0) + "s")
            res
          }
        }
      }
    }

    Primitives.add(cf)
  }
}
