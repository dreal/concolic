(*
Author: Soonho Kong   <soonhok@cs.cmu.edu>
        Wei Chen      <weichen1@andrew.cmu.edu>
        Sicun Gao     <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Wei Chen, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*)
type t = {lineno:    int;
            func_name: string;
            args:      string list;
            info:      string list}
val of_string : string -> t
val print : 'a BatIO.output -> t -> unit
