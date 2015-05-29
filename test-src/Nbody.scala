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

object NBody {

  def main(args: Array[String]): Unit = {

    DeliteBridge.install()

    def test(prog: String): Unit = {
      val res = RContext.eval(RContext.parseFile(
        new ANTLRInputStream(new ByteArrayInputStream(prog.getBytes))))

      println(res.pretty)
      println(res)
      // assert(res.pretty == "1, 2, 3")
    }

    test("""
 


  Delite({

pi <- 3.141592653589793         
solar_mass <- 4 * pi * pi           #ok
days_per_year <- 365.24
n_bodies <- 5

body_x <- c(
    0, # sun
    4.84143144246472090e+00, # jupiter
    8.34336671824457987e+00, # saturn
    1.28943695621391310e+01, # uranus
    1.53796971148509165e+01 # neptune
)
body_y <- c(
    0, # sun
    -1.16032004402742839e+00, # jupiter         #ok
    4.12479856412430479e+00, # saturn
    -1.51111514016986312e+01, # uranus          #ok
    -2.59193146099879641e+01 # neptune          #ok
)
body_z <- c(
    0, # sun
    -1.03622044471123109e-01, # jupiter         #ok
    -4.03523417114321381e-01, # saturn          #ok
    -2.23307578892655734e-01, # uranus          #ok
    1.79258772950371181e-01 # neptune
)

body_vx <- c(
    0, # sun
    1.66007664274403694e-03 * days_per_year, # jupiter          #ok 
    -2.76742510726862411e-03 * days_per_year, # saturn          #ok
    2.96460137564761618e-03 * days_per_year, # uranus           #ok
    2.68067772490389322e-03 * days_per_year # neptune           #ok
)
body_vy <- c(
    0, # sun
    7.69901118419740425e-03 * days_per_year, # jupiter          #ok
    4.99852801234917238e-03 * days_per_year, # saturn           #ok
    2.37847173959480950e-03 * days_per_year, # uranus           #ok
    1.62824170038242295e-03 * days_per_year # neptune           #ok
)
body_vz <- c(
    0, # sun
    -6.90460016972063023e-05 * days_per_year, # jupiter         #ok
    2.30417297573763929e-05 * days_per_year, # saturn           #ok
    -2.96589568540237556e-05 * days_per_year, # uranus          #ok
    -9.51592254519715870e-05 * days_per_year # neptune          #ok
)

body_mass <- c(
    solar_mass, # sun
    9.54791938424326609e-04 * solar_mass, # jupiter         #ok
    2.85885980666130812e-04 * solar_mass, # saturn          #ok
    4.36624404335156298e-05 * solar_mass, # uranus          #ok
    5.15138902046611451e-05 * solar_mass # neptune          #ok
)

offset_momentum <- function() {
    body_vx[[1]] <<- -sum(body_vx * body_mass) / solar_mass
    body_vy[[1]] <<- -sum(body_vy * body_mass) / solar_mass
    body_vz[[1]] <<- -sum(body_vz * body_mass) / solar_mass
}

advance <- function(dt) {
    dxx <- outer(body_x, body_x, "-") # ~2x faster then nested for loops
    dyy <- outer(body_y, body_y, "-")
    dzz <- outer(body_z, body_z, "-")
    distance <- sqrt(dxx * dxx + dyy * dyy + dzz * dzz)
    mag <- dt / (distance * distance * distance) # ~fast as distance^3
    diag(mag) <- 0
    body_vx <<- body_vx - as.vector((dxx * mag) %*% body_mass)
    body_vy <<- body_vy - as.vector((dyy * mag) %*% body_mass)
    body_vz <<- body_vz - as.vector((dzz * mag) %*% body_mass)
    body_x <<- body_x + dt * body_vx
    body_y <<- body_y + dt * body_vy
    body_z <<- body_z + dt * body_vz
}

energy <- function() {
    dxx <- outer(body_x, body_x, "-")
    dyy <- outer(body_y, body_y, "-")
    dzz <- outer(body_z, body_z, "-")
    distance <- sqrt(dxx * dxx + dyy * dyy + dzz * dzz)
    q <- (body_mass %o% body_mass) / distance
     return(sum(0.5 * body_mass *
              (body_vx * body_vx + body_vy * body_vy + body_vz * body_vz)) -
           sum(q[upper.tri(q)]))
}


nbody <- function(args) {
    n = if (length(args)) as.integer(args[[1]]) else 1000L
  #  options(digits=9)
    offset_momentum()
    cat(energy(), "\n")
    for (i in 1:n){
        advance(0.01)
        print(body_x)
        print(body_y)
        print(body_z)
        print(body_vx)
        print(body_vy)
        print(body_vz)
    }
    cat(energy(), "\n")
}

nbody(1)

    })
    """)

  }
}
