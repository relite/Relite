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
import r.builtins.{CallFactory,Primitives}
import r.nodes._
import r.nodes.truffle.{BaseR, RNode}
import com.oracle.truffle.api.frame._;

import org.antlr.runtime._

import java.io._

import scala.collection.JavaConversions._

import ppl.dsl.optiml.{OptiMLApplication,OptiMLCodeGenScala}
import ppl.delite.framework.transform._
import scala.virtualization.lms.common.StaticData
import ppl.delite.framework.datastructures.DeliteArray

import scala.collection.mutable._


trait Eval extends OptiMLApplication with StaticData {
  type Env = Map[RSymbol,Rep[Any]]
  var env: Env = Map.empty
  
   //storing declared functions
  type EnvFunct=Map[RSymbol, Function]
  var envFunctions:EnvFunct=Map.empty
  
  var globalEnv:scala.collection.immutable.Map[RSymbol,Rep[Any]]=scala.collection.immutable.Map.empty

  def infix_tpe[T](x:Rep[T]): Manifest[_]

  //def fun[A,B](f: Rep[A]=>Rep[B]):Rep[A=>B]
  def nuf[A,B](f: Rep[A=>B]):Rep[A]=>Rep[B]



  def liftValue(v: Any): Rep[Any] = v match {
    case v: RString => unit(v.getString(0))
    case v: ScalarIntImpl => unit(v.getInt(0))
    case v: ScalarDoubleImpl => unit(v.getDouble(0))
    case v: IntImpl => 
      val data = staticData(v.getContent).asInstanceOf[Rep[DeliteArray[Int]]]
      densevector_obj_fromarray(data, true)
    case v: DoubleImpl => 
      val data = staticData(v.getContent).asInstanceOf[Rep[DeliteArray[Double]]] 
      densevector_obj_fromarray(data, true)
    //representing boolean
    case v: RLogical => val intLogicalVal=v.getLogical(0)
                        if(intLogicalVal==1) unit(true) else unit(false) 
  }

  def convertBack(x: Any): AnyRef = x match {
    case x: String => RString.RStringFactory.getScalar(x)
    case x: Int => RInt.RIntFactory.getScalar(x)
    case x: Double => RDouble.RDoubleFactory.getScalar(x)
    // struct classes are generated on the fly. we cannot acces them yet.
    case x if x.getClass.getName == "generated.scala.DenseVectorInt" => RInt.RIntFactory.getFor(x.asInstanceOf[{val _data: Array[Int]}]._data)
    case x if x.getClass.getName == "generated.scala.DenseVectorDouble" => RDouble.RDoubleFactory.getFor(x.asInstanceOf[{val _data: Array[Double]}]._data)
//    case x: generated.scala.DenseVectorDouble => RDouble.RDoubleFactory.getFor(x._data)
    case () => RInt.RIntFactory.getScalar(0)
  }


  def evalFun[A:Manifest,B:Manifest](e: ASTNode, frame: Frame): Rep[A] => Rep[B] = e match {
    case e: Function => 
      { 
	x: Rep[A] => 
        val ex = RContext.createRootNode(e,null).execute(frame)
        ex match {
          case ex: ClosureImpl =>
            val env0 = env
            // TODO: closure env?
            env = env.updated(ex.function.paramNames()(0),x)
            val res = eval(ex.function.body.getAST, ex.enclosingFrame)
            env = env0
            res.asInstanceOf[Rep[B]]
        }
      }
  }
  
  //casting function
  def cast[A : Manifest](value: Rep[Any]): Rep[A] = {
    value.asInstanceOf[Rep[A]]
  }

  def eval(e: ASTNode, frame: Frame): Rep[Any] = e match {
    case e: Constant => liftValue(e.getValue )
     case e: SimpleAssignVariable =>
      val lhs = e.getSymbol
      val rhs=e.getExpr
      rhs match{
        case rhs:Function=> 
          envFunctions=envFunctions.updated(lhs, rhs) 
        case _=>    
          val rhss = eval(rhs,frame)
          env = env.updated(lhs,rhss)  
      }
    case e: SimpleAccessVariable =>
      val lhs = e.getSymbol
      env.getOrElse(lhs, {
        val ex = RContext.createRootNode(e,null).execute(frame)
        liftValue(ex)
      })
    case e: Sequence => 
      e.getExprs.map(g => eval(g,frame)).last
    case e: Add =>
      val lhs = eval(e.getLHS,frame)
      val rhs = eval(e.getRHS,frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      (lhs.tpe,rhs.tpe) match {
        case (D,D) => lhs.asInstanceOf[Rep[Double]] + rhs.asInstanceOf[Rep[Double]]
        case (VD,VD) => lhs.asInstanceOf[Rep[DenseVector[Double]]] + rhs.asInstanceOf[Rep[DenseVector[Double]]]
        case (VD,D) => lhs.asInstanceOf[Rep[DenseVector[Double]]] + rhs.asInstanceOf[Rep[Double]]
        case (VM, VM) => lhs.asInstanceOf[Rep[DenseMatrix[Double]]] + rhs.asInstanceOf[Rep[DenseMatrix[Double]]]
      }
    case e: Mult =>
      val lhs = eval(e.getLHS,frame)
      val rhs = eval(e.getRHS,frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      (lhs.tpe,rhs.tpe) match {
        case (D,D) => lhs.asInstanceOf[Rep[Double]] * rhs.asInstanceOf[Rep[Double]]
        case (VD,VD) =>   
          val lhs1=lhs.asInstanceOf[Rep[DenseVector[Double]]]
          val rhs1=rhs.asInstanceOf[Rep[DenseVector[Double]]]
          (lhs1.Clone*rhs1.Clone).asInstanceOf[Rep[DenseVector[Double]]]
        case (VD,D) => lhs.asInstanceOf[Rep[DenseVector[Double]]] * rhs.asInstanceOf[Rep[Double]]
        case (VM, VM) =>
          (rhs.asInstanceOf[Rep[DenseMatrix[Double]]] *:* lhs.asInstanceOf[Rep[DenseMatrix[Double]]]).asInstanceOf[Rep[DenseMatrix[Double]]] 
         case (VD,VM) =>
           val vector=lhs.asInstanceOf[Rep[DenseVector[Double]]]
           val matrix=rhs.asInstanceOf[Rep[DenseMatrix[Double]]]
           val vectorSize=vector.length
           val matrixRows=matrix.numRows
           val matrixCols=matrix.numCols
           val res=matrix.mutable
           var i=0
           while(i<matrixRows){
             var j=0
             while(j<matrixCols){
               res(i,j)=res(i,j)*vector(i % vectorSize)
               j+=1
             }
             i+=1
            }
            res
      }
      
    case e: Div =>
      val lhs = eval(e.getLHS,frame)
      val rhs = eval(e.getRHS,frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      val VM = manifest[DenseMatrix[Double]]
      (lhs.tpe,rhs.tpe) match {
        case (D,D) => lhs.asInstanceOf[Rep[Double]] / rhs.asInstanceOf[Rep[Double]]
        case (VD,VD) => lhs.asInstanceOf[Rep[DenseVector[Double]]] / rhs.asInstanceOf[Rep[DenseVector[Double]]]
        case (VD,D) => lhs.asInstanceOf[Rep[DenseVector[Double]]] / rhs.asInstanceOf[Rep[Double]]
        case (D, VM) => 
          val matrix=rhs.asInstanceOf[Rep[DenseMatrix[Double]]]
          val num=lhs.asInstanceOf[Rep[Double]]
          matrix.map(a => num/a)
      }
      
    //subtraction
     case e:Sub =>
       val lhs=eval(e.getLHS, frame)
       val rhs=eval(e.getRHS, frame)
       val VD=manifest[DenseVector[Double]]
       (lhs.tpe, rhs.tpe) match {
       	 case(D, D)=> 
           val v1=cast[Double](lhs)
           val v2=cast[Double](rhs)
           cast[Double](v1-v2)
         case (VD, VD) =>
           val v1=lhs.asInstanceOf[Rep[DenseVector[Double]]]
           val v2=rhs.asInstanceOf[Rep[DenseVector[Double]]]
           (v1 - v2).asInstanceOf[Rep[DenseVector[Double]]]
        }
      
    case e: Colon =>
      val lhs = eval(e.getLHS,frame)
      val rhs = eval(e.getRHS,frame)
      val D = manifest[Double]
      val VD = manifest[DenseVector[Double]]
      (lhs.tpe,rhs.tpe) match {
        case (D,D) => 
          indexvector_range(lhs.asInstanceOf[Rep[Double]].toInt,rhs.asInstanceOf[Rep[Double]].toInt+1).toDouble
      }

 

    case e: FunctionCall =>
      e.getName.toString match {
        case "map" | "sapply" =>
          val v = eval(e.getArgs.getNode(0), frame).asInstanceOf[Rep[DenseVector[Double]]]
          val f = evalFun[Double,Double](e.getArgs.getNode(1), frame)
          v.map(f)
        case "sum" => 
          val v = eval(e.getArgs.getNode(0), frame).asInstanceOf[Rep[DenseVector[Double]]]
          v.sum

	//Vector creation
	case "c" =>
          val first=eval(e.getArgs.getNode(0), frame)
          val sizeVect=e.getArgs.size()
          val v1=DenseVector[Double](e.getArgs.size(), true)

 	  for (i <- (0 until sizeVect)) {
            v1(i)=eval(e.getArgs.getNode(i),frame).asInstanceOf[Rep[Double]]
          }
          v1
      
        //function as.vector
        case "as.vector" =>
          val myArg=eval(e.getArgs.getNode(0), frame)
          if(myArg.isInstanceOf[Rep[DenseVector[Double]]])
            myArg.asInstanceOf[Rep[DenseVector[Double]]]
          else if(myArg.isInstanceOf[Rep[DenseMatrix[Double]]]){
            val matrix=myArg.asInstanceOf[Rep[DenseMatrix[Double]]]
            val vectSize=matrix.numRows*matrix.numCols
            val res=DenseVector[Double](vectSize, true)
            var ii=0
            while(ii < matrix.numRows){
              var jj=0
              while(jj < matrix.numCols){
                res(matrix.numCols*ii+jj)=matrix(ii,jj)
                jj+=1
              }
              ii+=1
            }
            res
          }
          else
            unit(())
        
        //function sqrt, for numbers and matrice
        case "sqrt" =>
          val arg=eval(e.getArgs.getNode(0), frame)
          val VD = manifest[DenseMatrix[Double]]
          val D = manifest[Double]
          arg.tpe match{
            case D =>
              val num=arg.asInstanceOf[Rep[Double]]
              sqrt(num)
            case VD=>
              val matrix=arg.asInstanceOf[Rep[DenseMatrix[Double]]]
              res=matrix.map(a => sqrt(a))
        }
        
        //function upper.tri
        case "upper.tri" =>
          val matrix=eval(e.getArgs.getNode(0), frame).asInstanceOf[Rep[DenseMatrix[Double]]]
          val resMatr=DenseMatrix[Boolean](matrix.numRows, matrix.numCols)
          var i=0
          while(i < matrix.numRows){
            var j=0
            while(j < matrix.numCols){
              if(i<j)
                resMatr(i,j)=true
              else
                resMatr(i,j)=false
              j+=1
           }
           i+=1
         }
         resMatr.asInstanceOf[Rep[DenseMatrix[Boolean]]]
         
        //function cat 
        case "cat" =>
          val args = e.getArgs.map(g => eval(g.getValue,frame)).toList
         for(arg<-args){
           print(arg+" ")
         }
        
        //function diag
         case "diag" =>
           val matrix=eval(e.getArgs.getNode(0), frame).asInstanceOf[Rep[DenseMatrix[Double]]]
           val diagonal=DenseVector[Double](matrix.numRows, true)
           var i=0
           while(i<matrix.numRows){
             diagonal(i)=matrix(i,i)
             i+=1
           }
           diagonal
         
        //function diag for assigment
        case "diag<-" =>
          val matrix=eval(e.getArgs.getNode(0), frame).asInstanceOf[Rep[DenseMatrix[Double]]]
          val number=eval(e.getArgs.getNode(1), frame).asInstanceOf[Rep[Double]]

          val invertEnv=env.map(_.swap)
          val theKey:RSymbol=invertEnv(matrix)
          val matrMut=cast[DenseMatrix[Double]](matrix.mutable)  
          
          var i=0
          while(i<matrMut.numRows){
            matrMut(i,i)=number
            i+=1
          }
          env=env.updated(theKey, cast[DenseMatrix[Double]](matrMut.Clone))
          unit(())
          
        //return
        //TODO: handle cases when return is in the middle of function body
       case "return" =>
         val value=eval(e.getArgs.getNode(0), frame)
         val D=manifest[Double]
         val I=manifest[Int]
         (value.tpe) match{
           case D=>cast[Double](value)
           case I=>cast[Int](value)
           case _=>value
         }

         
       case "as.integer" =>
         val arg=eval(e.getArgs.getNode(0), frame) 
         val D=manifest[Double]
         (arg.tpe) match{
           case D=> ((arg.asInstanceOf[Rep[Double]])toInt).asInstanceOf[Rep[Int]]
         } 
         
        //function uoter
        case "outer" =>
          val args=e.getArgs
          val v1=eval(args.getNode(0), frame).asInstanceOf[Rep[DenseVector[Double]]]
          val v2=eval(args.getNode(1), frame).asInstanceOf[Rep[DenseVector[Double]]]
          val op=eval(args.getNode(2), frame)
          val VD = manifest[DenseVector[Double]]
          (v1.tpe, v2.tpe) match {
            case (VD,VD) =>
            if(op=="-"){
              val res=DenseMatrix[Double](v1.length, v2.length)
              var i=0
              while(i<v1.length){
              var j=0
              while(j<v2.length){
                res(i,j)=(v1(i) - v2(j)).asInstanceOf[Rep[Double]]
                j+=1
              }
              i+=1
            }
            res
          }
          else{ //the default case
            val res=DenseMatrix[Double](v1.length, v2.length)
            var i=0
            while(i<v1.length){
              var j=0
              while(j<v2.length){
                res(i,j)=(v1(i) * v2(j)).asInstanceOf[Rep[Double]]
                j+=1
              }
              i+=1
            }
            res
          }
       }
        
        //function exists
      	case "exists"=>
          val name:String=e.getArgs.getNode(0).toString //name of the value, we are searching for, string
          val keys=env.keySet
          var isPresent:Rep[Boolean]=unit(false)
          for(k<-keys){
            if(k.name.toString.equals(name)) isPresent=unit(true)
          }
          isPresent
        
        //function length  
         case "length"=>
           val VD=manifest[DenseVector[Double]]
           val D=manifest[Double]
           val arg=eval(e.getArgs.getNode(0), frame)
           (arg.tpe) match{
             case VD=>((arg.asInstanceOf[Rep[DenseVector[Double]]]).length).asInstanceOf[Rep[Int]]
             case D=>val value=arg.asInstanceOf[Rep[Double]]; ((value/value).toInt).asInstanceOf[Rep[Int]]
             case _=> val value=arg.asInstanceOf[Rep[Double]]; ((value-value).toInt).asInstanceOf[Rep[Int]]
           }
        
          //function options
          //TODO: fix/complete it. This doesn't work for now
          case "options"=>
          val arg=e.getArgs.getNode(0)
          val I=manifest[Int]
          (arg) match{
            case arg:Constant=>
              val const=eval(arg, frame)
          //    (const.tpe) match{
          //      case I=>digits=const.toInt //here digits should be some global value
          //      unit(())
          //    }
          }

        
      	//calls of defined functions
      	//not working for arguments with default values yet
        case _ =>
          val keys=envFunctions.keySet
          val callName=e.getName.toString
          if(keys.contains(e.getName)){
            val functionNode=envFunctions(e.getName)
            val signature=functionNode.getSignature
            val arguments=e.getArgs
            
            var currentEnv = env.clone
            
       	    val realNrArgs=arguments.size
            val expectedNrArgs=signature.size
            if(realNrArgs==expectedNrArgs){
              val argNames = signature.map(g => g.getName).toList
              for(i<-(0 until realNrArgs)){
                env=env.updated(argNames(0), eval(arguments.getNode(i), frame))
              }
              val result=eval(functionNode.getBody, frame)
              globalEnv.foreach(pair=> currentEnv.update(pair._1, pair._2))
              env=currentEnv
              globalEnv=scala.collection.immutable.Map.empty
              result

            }
            else{
              println("Error in function call")
            }
          }
          else{
            val args = e.getArgs.map(g => eval(g.getValue,frame)).toList
            (e.getName.toString,args) match {
              case ("Vector.rand",(n:Rep[Double])::Nil) => 
                assert(n.tpe == manifest[Double])
                Vector.rand(n.toInt)
              case ("pprint",(v:Rep[DenseVector[Double]])::Nil) => 
                assert(v.tpe == manifest[DenseVector[Double]])
                v.pprint
              case s => println("unknown f: " + s + " / " + args.mkString(",")); 
            }
         }
      }
      

     //vectors outer product, just for vectors of double for now
     case e:OuterMult=>val firstVect=eval(e.getLHS, frame)
       val secondVect=eval(e.getRHS, frame)
       val VD = manifest[DenseVector[Double]]
       (firstVect.tpe,secondVect.tpe) match {
         case (VD,VD) =>(firstVect.asInstanceOf[Rep[DenseVector[Double]]] ** secondVect.asInstanceOf[Rep[DenseVector[Double]]]).asInstanceOf[Rep[DenseMatrix[Double]]]                
       }
             
             
      //matrix multiplication, just for double for now                  
      case e:MatMult=>
        val matr1=eval(e.getLHS, frame)
        val matr2=eval(e.getRHS, frame)
        val VM=manifest[DenseMatrix[Double]]
        val VD=manifest[DenseVector[Double]]
        (matr1.tpe, matr2.tpe) match{
          case(VM, VM) => 
            (matr1.asInstanceOf[Rep[DenseMatrix[Double]]] *:* matr2.asInstanceOf[Rep[DenseMatrix[Double]]]).asInstanceOf[Rep[DenseMatrix[Double]]] 
          case(VM, VD) => 
            val vect=matr2.asInstanceOf[Rep[DenseVector[Double]]]
            val matr=matr1.asInstanceOf[Rep[DenseMatrix[Double]]]
            (matr.mapRowsToVector(row=>sum(row * vect))).asInstanceOf[Rep[DenseMatrix[Double]]]
        }


     //just for single double for now
     case e: UnaryMinus=> 
       val lhs=eval(e.getLHS, frame)
       val D = manifest[Double]
       val VD = manifest[DenseVector[Double]]
       lhs.tpe match{
         case D=>(-1*lhs.asInstanceOf[Rep[Double]])
       }


     //if node - with or witouth else
     case e:If=>
      val cond=eval(e.getCond, frame)
      val trueCase=eval(e.getTrueCase, frame)
      val falseCase=eval(e.getFalseCase, frame)
      val D=manifest[Double]
      val B=manifest[Boolean]
      val I=manifest[Int]
       cond.tpe match{
        case B=>
          val condition=cast[Boolean](cond)
          (trueCase.tpe, falseCase.tpe) match{
            case (D,D)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (I,I)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (I,D)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (D,I)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (_,_)=>
              if(condition) cast[AnyVal](trueCase) else cast[AnyVal](falseCase)
          }
        case I=>
          val condition=cast[Boolean](cast[Int](cond)!=0)
           (trueCase.tpe, falseCase.tpe) match{
            case (D,D)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (I,I)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (I,D)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (D,I)=>
              if(condition) cast[Double](trueCase) else cast[Double](falseCase)
            case (_,_)=>
              if(condition) cast[AnyVal](trueCase) else cast[AnyVal](falseCase)
          }

      }
      

      //access double value vector node
      case e: AccessVector=>
        val vect=eval(e.getVector, frame)
        val arg=eval(e.getArgs.getNode(0), frame)
        val VD=manifest[DenseVector[Double]]
        val VM=manifest[DenseMatrix[Double]]
        val D=manifest[Double]
        val BM=manifest[DenseMatrix[Boolean]]
        (vect.tpe) match{
          case VD=>
            (arg.tpe) match{
              case D=> 
                val ind:Rep[Int]=arg.asInstanceOf[Rep[Int]]
                vect.asInstanceOf[Rep[DenseVector[Double]]](ind.toInt).asInstanceOf[Rep[Double]]
            }
            case D=> vect.asInstanceOf[Rep[Double]]
            case VM =>
              (arg.tpe) match{
                case BM=>
                  val matrix=vect.asInstanceOf[Rep[DenseMatrix[Double]]]
                  val upperTriMatr=arg.asInstanceOf[Rep[DenseMatrix[Boolean]]]
                  val rows=matrix.numRows
                  val cols=matrix.numCols
                  val dim=rows*cols
                  val resultVect=DenseVector[Double](dim, true)
                  var i=0
                  var count=0
                  while(i<dim){
                    if(upperTriMatr(i%cols, i/cols)){
                      resultVect(count)=matrix(i%cols, i/cols)
                      count+=1
                    }
                    i+=1
                  } 
                (resultVect.take(count)).asInstanceOf[Rep[DenseVector[Double]]]
            }
          }
      
      
      //update double value vector node
      case e:UpdateVector=>
        val rhs=cast[Double](eval(e.getRHS, frame))
        val accessVector=e.getVector
        val vect=cast[DenseVector[Double]](eval(accessVector.getVector, frame))
        val arg=cast[Int](eval(accessVector.getArgs.getNode(0), frame))
        val index=(arg.toInt-1).toInt

        val invertEnv=env.map(_.swap)
        val theKey:RSymbol=invertEnv(vect)

        val vectMut=DenseVector[Double](vect.length, true)
        var i=0
        while(i<index){
          vectMut(i)=vect(i)
          i+=1
        }
        vectMut(index)=rhs
        i+=1
        while(i<vect.length){
          vectMut(i)=vect(i)
          i+=1
        }
        if(e.isSuper())
          globalEnv=globalEnv.updated(theKey, vectMut)
        else
          env=env.updated(theKey, vectMut.Clone)
      

     //for loop
     case e:For=>
       val body=e.getBody   //type: ASTNode
       var envBeforeLoop: EnvCurrFunctLoop = env.clone
       val counter=e.getCVar//type:RSymbol
       val range:Rep[DenseVector[Double]]=eval(e.getRange, frame).asInstanceOf[Rep[DenseVector[Double]]] //type:ASTNode
       val bodyEvaluated:Rep[Any]=unit(())
       for(currVal <- range) {
         env=env.updated(counter, currVal)
         bodyEvaluated=eval(body, frame)
       }
       env=envBeforeLoop
       bodyEvaluated
       
    //not node-just for single boolean, for now
    case e:Not=>
      val lhs=eval(e.getLHS, frame)
      val B = manifest[Boolean]
      lhs.tpe match{
        case B=> !lhs.asInstanceOf[Rep[Boolean]]
      
      
     //elementwise and - just for simple boolean values, not vectors, for now   
     case e: ElementwiseAnd=>
       val lhs=eval(e.getLHS, frame)
       val rhs=eval(e.getRHS, frame)
       val B = manifest[Boolean]
       (lhs.tpe,rhs.tpe) match {
         case (B,B) => (lhs.asInstanceOf[Rep[Boolean]] && rhs.asInstanceOf[Rep[Boolean]]).asInstanceOf[Rep[Boolean]]
       }

    //elementwise or - just for simple boolean values, not vectors, for now   
    case e: ElementwiseOr=>
      val lhs=eval(e.getLHS, frame)
      val rhs=eval(e.getRHS, frame)
      val B = manifest[Boolean]
      (lhs.tpe,rhs.tpe) match {
        case (B,B) => lhs.asInstanceOf[Rep[Boolean]] || rhs.asInstanceOf[Rep[Boolean]]
      }
      
    
    //integer division - just for simple values for now
    case e: IntegerDiv=>
      val lhs=eval(e.getLHS, frame)
      val rhs=eval(e.getRHS, frame)
      val D = manifest[Double]
      (lhs.tpe,rhs.tpe) match {
        case (D,D) => (lhs.asInstanceOf[Rep[Double]] / rhs.asInstanceOf[Rep[Double]]).toInt.asInstanceOf[Rep[Int]]
      }
        
    case _ => 
      println("unknown: "+e+"/"+e.getClass); 
      new RLanguage(e) //RInt.RIntFactory.getScalar(42)
      42
  }
}
  
class EvalRunner extends MainDeliteRunner with Eval { self =>
  //case class Lam[A,B](f: Rep[A]=>Rep[B]) extends Def[A=>B]
  //override def fun[A:Manifest,B:Manifest](f: Rep[A]=>Rep[B]):Rep[A=>B] = Lam(f)
  def nuf[A,B](f: Rep[A=>B]):Rep[A]=>Rep[B] = f match { case Def(Lambda(f,_,_)) => f }

  def infix_tpe[T](x:Rep[T]): Manifest[_] = x.tp

  appendTransformer(new LoopTransformer { val IR: self.type = self })
  appendTransformer(new PrefixSumTransformer { val IR: self.type = self })

  val transport = new Array[Any](1)
  def setResult(x: Rep[Any]) = staticData(transport).update(0,x)
  def getResult: AnyRef = convertBack(transport(0))
}


trait LoopTransformer extends ForwardPassTransformer with OptiMLCodeGenScala {
  val IR: MainDeliteRunner
  import IR._

  stream = new PrintWriter(System.out)
  override def traverseStm(stm: Stm) = stm match {
    case TTP(sym, mhs, rhs: AbstractFatLoop) => 
      (sym,mhs).zipped.foreach((s,p) => traverseStm(TP(s,p)))
    case _ =>
      super[ForwardPassTransformer].traverseStm(stm)
  }
}

trait PrefixSumTransformer extends LoopTransformer {
  val IR: MainDeliteRunner
  import IR._

  override def traverseStm(stm: Stm) = stm match {
    case TTP(sym::Nil, mhs, outer: AbstractFatLoop) => 
      outer.body match {
        case (body: DeliteCollectElem[a,i,ca])::Nil if body.cond.isEmpty =>
          implicit val (ma,mi,mca) = (body.mA, body.mI, body.mCA)
          def loopVarUsedIn(bs: List[Block[Any]], vy: Sym[Any]) = 
            getFreeVarBlock(Block(Combine(bs.map(getBlockResultFull))),vy::Nil).contains(outer.v)
          getBlockResult(body.func) match {
            case Def(Forward(Def(Loop(Def(IntPlus(Const(1), outer.v)), vy, bodyr: DeliteReduceElem[a])))) 
            if bodyr.cond.isEmpty && !loopVarUsedIn(bodyr.zero::bodyr.func::bodyr.rFunc::Nil, vy) =>
              implicit val ma = bodyr.mA

              case object PrefixReduce extends DeliteOpSingleTask(reifyEffects {
                val data = withSubstScope(body.sV -> outer.size) { reflectBlock(body.allocN) }
                val zero = reflectBlock(bodyr.zero)

                def fold(i: Rep[Int], e: Rep[a]): Rep[a] = {
                  val a = withSubstScope(vy -> i)                      { reflectBlock(bodyr.func)  }
                  withSubstScope(bodyr.rV._1 -> e, bodyr.rV._2 -> a)   { reflectBlock(bodyr.rFunc) }
                }

                def update(i: Rep[Int], e: Exp[a]) =
                  withSubstScope(body.allocVal -> data, outer.v -> i, body.eV -> e) { reflectBlock(body.update) }

                var i = 0
                var acc = zero

                while (i < outer.size) {
                  val e = fold(i,readVar(acc))
                  update(i, e)
                  acc = e
                  i = i + 1
                }

                withSubstScope(body.allocVal -> data) { reflectBlock(body.finalizer) }
              })
              subst += (sym -> reflectPure(PrefixReduce))
            case _ =>
          }
        case _ =>
      }
    case _ =>
      super[LoopTransformer].traverseStm(stm)
  }
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

        val ast1:AnyRef = ast // apparently ASTNode member fields are reassigned -- don't make it look like one!
        new BaseR(call) { 
          def execute(frame: Frame): AnyRef = {
            val ast = ast1.asInstanceOf[ASTNode]
            println("delite input: "+ast)

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
            println("elapsed: " + ((t1-t0)/1000.0) + "s")
            res
          }
        }
      }
    }

    Primitives.add(cf)
  }
}
