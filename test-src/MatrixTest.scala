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
import r.nodes.ast._
import r.nodes.exec.{ BaseR, RNode }
import r.runtime._;

import org.antlr.runtime._

import java.io._

import scala.collection.JavaConversions._

object MatrixTest {

  def main(args: Array[String]): Unit = {

    DeliteBridge.install()

    def test(prog: String): Unit = {
      val res = RContext.eval(RContext.parseFile(
        new ANTLRInputStream(new ByteArrayInputStream(prog.getBytes))))
    }

    test("""
 

      Delite({
        m <- matrix(c(1,2,3,4,5,6,7,8), 2, 4)
        print(m)
      })

      """)

  }
}