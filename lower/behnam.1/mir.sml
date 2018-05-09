structure MIR = 
struct

structure A = AST
type symbol = A.symbol
exception InternalError of string
exception SemanticError of string
exception NotImplemented

(* -- Different kinds of instructions
      Notice that they are all about control flow, except for the MOVE *)
datatype inst = LABEL of A.symbol
              | MOVE of tree * tree
              | CALL of A.symbol * A.symbol * tree list
              | RET of tree
              | JUMP of A.symbol
              | CJUMP of cmpop * tree * tree * A.symbol

(* -- Expression trees
      All computation, no control flow *)
and tree = IMM of int
         | OFFSET of A.symbol
         | STRING of string
         | MEM of tree
         | VAR of A.symbol
         | BINOP of binop * tree * tree
         | EMPTY

and binop = PLUS | MINUS | TIMES | DIV
and cmpop = EQ | NEQ | LT | LE | GT | GE

(* -- Gensym function
      Not exactly perfect, but good enough *)

val uid = ref 0

val gensym : string -> A.symbol =
fn base =>
    let val cur_uid = ref (! uid)
        val newsym = (base, 0, 0, cur_uid)
    in ( uid := !uid + 1;
         newsym )
    end

(* -- Representation for a function
      a FUNDECL and a list of instructions  *)

datatype funrep = FUN of { fundecl: A.decl, impl: inst list }


(* -- Lower a comparative operation from AST to cmpop -- *)

	                    fun lowerOp (A.EQ) = EQ
			      | lowerOp (A.NEQ) = NEQ
			      | lowerOp (A.LT) = LT
			      | lowerOp (A.LE) = LE
			      | lowerOp (A.GT) = GT
			      | lowerOp (A.GE) = GE


(* -- Lower an expression
      Since everything is an expression, this function must be able to generate
      MIR instructions, expressions, as well as new function definitions.
      The strategy is as follows: every call to lowerExp *must* produce a piece
      of an exp, even if it is just a temp var

      Input: a fragment of AST
      Output: a tuple of three things:
               - a tree that represents the value of the expression
               - a list of instructions that help compute the tree value
               - a list of any functions encountered in the translation
  *)

fun lowerExp (A.NIL) =                      (IMM(0),    [], [])
 |  lowerExp (A.INT(value, pos, line)) =    (IMM(value), [], [])
 |  lowerExp (A.STRING(value, pos, line)) = (STRING(value), [], [])
 |  lowerExp (A.VAR(sym)) =                 (VAR(sym),  [], [])

 |  lowerExp (A.DOT(exp, field)) = 
                let 
                    val (exp_tree, exp_ins, exp_funs) = lowerExp exp
                    val new_tree = MEM( BINOP( PLUS, exp_tree, OFFSET field) )
                in
                    (new_tree, exp_ins, exp_funs)
                end

 |  lowerExp (A.SUBSCRIPT(arr, index)) = 
		let
		    val (effective_array_tree, array_ins, array_funs) = lowerExp arr
		    val (effective_index_tree, index_ins, index_funs) = lowerExp index
		    val new_tree = MEM( BINOP( PLUS, effective_array_tree, BINOP(TIMES, effective_index_tree, IMM(8) )  ) )
		in
		    (new_tree, array_ins @ index_ins, array_funs @ index_funs)
		end

(* FIXME: only the first exp is returned! *)
 |  lowerExp (A.SEQ(exps)) =
		let
		    fun expAdd (exp, (_, other_ins, other_funs)) = 
		        let
			    val (new_exp_tree, new_exp_ins, new_exp_funs) = lowerExp exp
			in
			    (new_exp_tree,new_exp_ins @ other_ins , other_funs @ new_exp_funs )
			end
		    val init = (EMPTY, [], [])
		in
		    foldr expAdd init exps
		end			   
		    		
(* FIXME: why -1 does not work as IMM? *)
 |  lowerExp (A.NEG(exp)) = 
		let
		   val (exp_tree, exp_ins, exp_funs) = lowerExp exp
		in
		    (BINOP(TIMES, exp_tree, IMM(1) ), exp_ins, exp_funs)
		end
(* FIXME: Order of arguments *)
 |  lowerExp (A.CALL(sym, args)) = 
		let
		    fun args2List (exp1, (exp_tree_list, exp_ins, exp_funs)) =
			let
			    val (exp1_tree, exp1_ins, exp1_funs) = lowerExp exp1
			in
			    (exp_tree_list @ [exp1_tree], exp_ins @ exp1_ins,  exp_funs @ exp1_funs)
			end
		    val init = ([], [], [])

		    val (args_tree_list, args_ins, args_funs) = foldr args2List init args

		    val ret_sym = gensym "new_call_sym"
		    val call_ins = CALL(sym, ret_sym, args_tree_list)
		in
		   (VAR(ret_sym), args_ins @ [call_ins], args_funs)
		end

 |  lowerExp (A.BINOP(e1, oper, e2)) = 
		let
(* FIXME: zero is returned *) 
		    val (e1_tree, e1_ins, e1_funs) = lowerExp e1
		    val (e2_tree, e2_ins, e2_funs) = lowerExp e2

		    fun lowerOp (A.PLUS)  =  ([BINOP(PLUS, e1_tree, e2_tree)], [])
		      | lowerOp (A.MINUS) =  ([BINOP(MINUS, e1_tree, e2_tree)], [])
		      | lowerOp (A.TIMES) =  ([BINOP(TIMES, e1_tree, e2_tree)], [])
		      | lowerOp (A.DIV)   =  ([BINOP(DIV, e1_tree, e2_tree)], [])

(*FIXME: COMPARISONS!*)
		      | lowerOp (A.EQ)    =  ([], [CJUMP(EQ, e1_tree, e2_tree, gensym "EQ")])
		      | lowerOp (A.NEQ)   =  ([], [CJUMP(NEQ, e1_tree, e2_tree, gensym "NEQ")])
		      | lowerOp (A.LT)    =  ([], [CJUMP(LT, e1_tree, e2_tree, gensym "LT")])
		      | lowerOp (A.LE)    =  ([], [CJUMP(LE, e1_tree, e2_tree, gensym "LE")])
		      | lowerOp (A.GT)    =  ([], [CJUMP(GT, e1_tree, e2_tree, gensym "GT")])
		      | lowerOp (A.GE)    =  ([], [CJUMP(GE, e1_tree, e2_tree, gensym "GE")])
		    val (binop_tree_list, binop_tree_ins)  = lowerOp(oper)
		    fun binop_tree ([]) = EMPTY
		      | binop_tree (h::tail) = h
		    
		in
		    (binop_tree(binop_tree_list), e1_ins @ e2_ins @ binop_tree_ins, e1_funs @ e2_funs)
		end
 |  lowerExp (A.MAKEARR(name, size, init)) = 
		let
		    val (size_tree, size_ins, size_funs) = lowerExp size
		    val (init_tree, init_ins, init_funs) = lowerExp init	
		    val arrmake_tree = MEM(BINOP(TIMES, size_tree, IMM(8)))
(* TODO: MOVE init_tree in memory for size_tree times 		
		   fun write_array_on_mem (size_tree) =
			let
			   val  counter = ref size_tree
			in
			  while !counter > 0 do (
		   	      counter := !counter - 1
			      MOVE( MEM(
					BINOP(PLUS, arraybase, BINOP(TIMES, IMM(counter), IMM(8))) 
				       ), 
				    init_tree
				  )
			      write_array_on_mem (counter)
		          )
			end
*)
		in
		    (arrmake_tree, size_ins@init_ins, size_funs@init_funs)
		end

 |  lowerExp (A.MAKEREC(name, inits)) =  

(* do we need to calculate the offset, or do we just call OFFSET on the fieldid to get the offset? *)
(* let OFFSET get offset *)
		let
		    val tree_name = VAR(name)
		    fun allocate([]) = []
		      | allocate([(id, exp)]) = 
			let
			    val (exp_tree, exp_ins, exp_funs) = lowerExp exp
			    val allocate_ins = MOVE(MEM(BINOP(PLUS, VAR(name), OFFSET(id))), exp_tree)
			in
			    (exp_ins @ [allocate_ins])
			end
		      | allocate ((id, exp) :: other_inits ) =
		    	    allocate([(id, exp)]) @ allocate(other_inits)
		    
		in
			(EMPTY, allocate (inits), []) (*FIXME: funs and tree? *)
		end




(* calculate offset:		let
		    val tree_name = VAR(name)
		    fun allocate ([(exp, id)], counter) =
			let
			    val (exp_tree, exp_ins, exp_funs) = lowerExp exp
			    val allocate_ins = MOVE(MEM(BINOP(PLUS, VAR(name), 
BINOP(TIMES, VAR(counter), IMM(8))

)), exp_tree)
			in
			    (exp_tree, exp_ins @ [allocate_ins], exp_funs)
			end
		      
		       |allocate((exp, id)::tail, counter) =
			let
			    val (exp_tree, exp_ins, exp_funs) = allocate((exp, id), counter + 1)
			    val (a, b, c) = allocate(tail, counter + 1)
			in
			    (EMPTY, exp_ins@b, exp_funs@c)
			end
		in
		    allocate(inits, 0)
		end
*)


 |  lowerExp (A.ASSIGN(lhs, rhs)) = 
                let val (left_tree, left_ins, left_funs) = lowerExp lhs
                    val (right_tree, right_ins, right_funs) = lowerExp rhs
                in
                    (EMPTY, left_ins @ 
                            right_ins @ 
                            [ MOVE(left_tree, right_tree) ], 
                     left_funs @ right_funs)
                end

 |  lowerExp (A.IF(cond, truebr, SOME(falsebr))) =
		let
		    val (truebr_tree, truebr_ins, truebr_funs) = lowerExp truebr
		    val (falsebr_tree, falsebr_ins, falsebr_funs) = lowerExp falsebr

		    val symbol_true = gensym "TRUE_BRANCH"
		    val ins_label_true = LABEL(symbol_true)
		
		    
		    val symbol_false = gensym "FALSE_BRANCH"
		    val ins_label_false = LABEL(symbol_false)		    
		    
		    val symbol_end = gensym "END"
		    val ins_label_end = LABEL(symbol_end)
		    val ins_jump_end = JUMP(symbol_end)
                    		  
 		    fun lowerCond (A.NIL, true_symb, false_symb) = (EMPTY, [], [])

		       |lowerCond(A.BINOP(subCondExp1, A.OR, subCondExp2), true_symb, false_symb) = 
			    let
				val or_symb = gensym "OR"
				val (sub1_tree, sub1_ins, sub1_funs) = lowerCond(subCondExp1, true_symb, or_symb)
				val (sub2_tree, sub2_ins, sub2_funs) = lowerCond(subCondExp2, true_symb, false_symb)
				val or_tree = VAR(gensym "OR_TREE")
				val or_ins = sub1_ins @ [LABEL(or_symb)] @ sub2_ins
				val or_funs = sub1_funs @ sub2_funs
			    in
				(or_tree, or_ins, or_funs)
			    end
		       |lowerCond(A.BINOP(subCondExp1, A.AND, subCondExp2), true_symb, false_symb) =
			    let
				val and_symb = gensym "AND"
				val (sub1_tree, sub1_ins, sub1_funs) = lowerCond(subCondExp1, and_symb, false_symb)
				val (sub2_tree, sub2_ins, sub2_funs) = lowerCond(subCondExp2, true_symb, false_symb)
				val and_tree = VAR(gensym "AND_TREE")
				val and_ins = sub1_ins @ [LABEL(and_symb)] @ sub2_ins
				val and_funs = sub1_funs @ sub2_funs
			    in
				(and_tree, and_ins, and_funs)
			    end
		       
		       |lowerCond (A.BINOP(condOperandExp1, oper ,condOperandExp2), true_symb, false_symb) =
			let 
			    val (condOperandExp1_tree, condOperandExp1_ins, condOperandExp1_funs) = 
				lowerExp (condOperandExp1)
			    val (condOperandExp2_tree, condOperandExp2_ins, condOperandExp2_funs) = 
				lowerExp (condOperandExp2)

			    val cjump_ins = 
			        CJUMP (lowerOp(oper),condOperandExp1_tree,condOperandExp2_tree,true_symb)
			    val jump_false_ins = JUMP(false_symb)

			    val base_ins = condOperandExp1_ins @ condOperandExp2_ins @ [cjump_ins] @ [jump_false_ins]
			    val base_funs = condOperandExp1_funs @ condOperandExp2_funs
			    val base_return_tree = MEM(VAR(gensym "BASE_CASE"))
			in
			    (base_return_tree, base_ins, base_funs)
			    
			end
			                       
		    val (return_tree, lowerCond_ins, lowerCond_funs) = lowerCond(cond, symbol_true, symbol_false)

		    val return_symb = gensym "RETURN_VALUE"

		    val ins_update_return_tru_br = MOVE (MEM(VAR (return_symb)), truebr_tree)
		    val ins_update_return_fls_br = MOVE (MEM(VAR(return_symb)), falsebr_tree)
		    val return_tree = MEM(VAR(return_symb))
		in
		  (return_tree, lowerCond_ins @ [ins_label_true] @ truebr_ins @ [ins_update_return_tru_br]  @ [ins_jump_end] @ [ins_label_false] @ falsebr_ins @ [ins_update_return_fls_br] @ [ins_label_end] , lowerCond_funs)
		end

 |  lowerExp (A.IF(cond, truebr, NONE)) =
		let
		    val (truebr_tree, truebr_ins, truebr_funs) = lowerExp truebr

		    val symbol_true = gensym "TRUE_BRANCH"
		    val ins_label_true = LABEL(symbol_true)
		
		    
		    val symbol_false = gensym "FALSE_BRANCH"
		    val ins_label_false = LABEL(symbol_false)		    
		    
		    val symbol_end = gensym "END"
		    val ins_label_end = LABEL(symbol_end)
		    val ins_jump_end = JUMP(symbol_end)
                    		  
 		    fun lowerCond (A.NIL, true_symb, false_symb) = (EMPTY, [], [])

		       |lowerCond(A.BINOP(subCondExp1, A.OR, subCondExp2), true_symb, false_symb) = 
			    let
				val or_symb = gensym "OR"
				val (sub1_tree, sub1_ins, sub1_funs) = lowerCond(subCondExp1, true_symb, or_symb)
				val (sub2_tree, sub2_ins, sub2_funs) = lowerCond(subCondExp2, true_symb, false_symb)
				val or_tree = VAR(gensym "OR_TREE")
				val or_ins = sub1_ins @ [LABEL(or_symb)] @ sub2_ins
				val or_funs = sub1_funs @ sub2_funs
			    in
				(or_tree, or_ins, or_funs)
			    end
		       |lowerCond(A.BINOP(subCondExp1, A.AND, subCondExp2), true_symb, false_symb) =
			    let
				val and_symb = gensym "AND"
				val (sub1_tree, sub1_ins, sub1_funs) = lowerCond(subCondExp1, and_symb, false_symb)
				val (sub2_tree, sub2_ins, sub2_funs) = lowerCond(subCondExp2, true_symb, false_symb)
				val and_tree = VAR(gensym "AND_TREE")
				val and_ins = sub1_ins @ [LABEL(and_symb)] @ sub2_ins
				val and_funs = sub1_funs @ sub2_funs
			    in
				(and_tree, and_ins, and_funs)
			    end
		       
		       |lowerCond (A.BINOP(condOperandExp1, oper ,condOperandExp2), true_symb, false_symb) =
			let 
			    val (condOperandExp1_tree, condOperandExp1_ins, condOperandExp1_funs) = 
				lowerExp (condOperandExp1)
			    val (condOperandExp2_tree, condOperandExp2_ins, condOperandExp2_funs) = 
				lowerExp (condOperandExp2)

			    val cjump_ins = 
			        CJUMP (lowerOp(oper),condOperandExp1_tree,condOperandExp2_tree,true_symb)
			    val jump_false_ins = JUMP(false_symb)

			    val base_ins = condOperandExp1_ins @ condOperandExp2_ins @ [cjump_ins] @ [jump_false_ins]
			    val base_funs = condOperandExp1_funs @ condOperandExp2_funs
			    val base_return_tree = MEM(VAR(gensym "BASE_CASE"))
			in
			    (base_return_tree, base_ins, base_funs)
			    
			end
			                       
		    val (return_tree, lowerCond_ins, lowerCond_funs) = lowerCond(cond, symbol_true, symbol_false)

		    val return_symb = gensym "RETURN_VALUE"

		    val return_tree = EMPTY
		in
		  (return_tree, lowerCond_ins @ [ins_label_true] @ truebr_ins @ [ins_jump_end] @ [ins_label_false] @ [ins_label_end] , lowerCond_funs)
		end

 |  lowerExp (A.WHILE(cond, body)) = 
			let
			    val (cond_tree, cond_ins, cond_funs) = lowerExp cond
			    val (body_tree, body_ins, body_funs) = lowerExp body
			    
			    val start_sym = gensym  "START_WHILE"
			    val end_sym = gensym "END_WHILE"
			
			    val start_label = LABEL start_sym
			    val cjump_check_ins = CJUMP(EQ, cond_tree, IMM(0), end_sym)
			    (* body_ins *)
			    val jump_top_ins = JUMP start_sym
			    val end_label = LABEL end_sym
			in
			    (EMPTY, cond_ins @ [start_label] @ [cjump_check_ins] @ body_ins @ [jump_top_ins] @ [end_label], cond_funs @ body_funs)
			end



 |  lowerExp (A.FOR(name, start, finish, body)) = 
			let
			    val index_tree = VAR(name)
			    val (start_tree, start_ins, start_funs) = lowerExp(start)
			    val (finish_tree, finish_ins, finish_funs) = lowerExp(finish)
			    val (body_tree, body_ins, body_funs) = lowerExp(body)

			    val start_symb  = gensym "START_LOOP"
			    val end_symb = gensym "END_LOOP"
			    
			    val init_tree_ins = MOVE(index_tree, start_tree)
			    val start_label = LABEL(start_symb)
			    val cjump_ins = CJUMP (GT, index_tree, finish_tree, end_symb)
			    (* body here *)
			    val inc_index = MOVE (index_tree, BINOP(PLUS, index_tree, IMM(1)))
			    val jump_start = JUMP start_symb
    			    val end_label = LABEL(end_symb)

			in
			    (EMPTY, start_ins @ finish_ins @ [init_tree_ins] @ [start_label] @ [cjump_ins] @ body_ins @ [inc_index] @ [jump_start] @ [end_label], start_funs @ finish_funs @ body_funs)
			end

			

 |  lowerExp (A.LET(decls, exprs)) =

(*  TODO: currently we only handle last item of the list
	we should find a way to recurse/ iterate on decls and exprs 
 	   fun starExp []  = (EMPTY, [], [])
               | starExp h_exp::t = 
			let 
				val (h_tree, h_ins, h_funs) = lowerExp h_exp
			in
				NIL
			end		    
*)
 	let 
	    val last_decl = (hd o rev) decls
	    val (decl_ins, decl_funs) = lowerDecl last_decl

	    val last_exp = (hd o rev) exprs
            val (exp_tree, exp_ins, exp_funs) = lowerExp last_exp
	in 
	    (exp_tree, decl_ins @ exp_ins, decl_funs @ exp_funs)
	end


 |  lowerExp (A.BREAK) = (EMPTY, nil, nil)(* TODO: Verify *)
		
(* -- Lower declarations
      There are only two things to handle here: variables, which have code to initialize them,
      and nested function definitions. Behnam: so no value (tree) needed here *)

and lowerDecl (A.VARDECL(sym, ty, exp)) =
    let val (exp_tree, exp_ins, exp_funs) = lowerExp exp
        val assign = MOVE(VAR(sym), exp_tree)
    in
        (exp_ins @ [ assign ], exp_funs)
    end

 |  lowerDecl (fundecl as A.FUNDECL(sym, args, ty, body)) = ([], lowerFun(fundecl))
 |  lowerDecl (_) = ([], [])

(* -- Lower a single function
      This code takes a single function, turns it into instructions,
      and adds it to the current list of functions in the program.   *)

and lowerFun (fundecl as A.FUNDECL(name, argdecls, resultty, body)) =
    let 
        val (tree, ins, funs) = lowerExp( body )
        val ret_ins = RET(tree)
        val all_ins = ins @ [ ret_ins ]
        val newfun = FUN{ fundecl=fundecl, impl=all_ins }
        
    in
        funs @ [ newfun ]
    end

 | lowerFun (_) = raise SemanticError("Attempt to lower a non-function declaration")

(* -- Lower the whole program
      We first wrap the top-level expression in a synthetic procedure called main. *)

fun lowerProgram(exp) =
    let 
        val main = A.FUNDECL( ("main", 0, 0, ref 0), [], NONE, exp )
    in
        lowerFun(main)
    end

(* -- MIR pretty printer *)

fun printSym (name, pos, line, uid) = 
    if !uid = 0 then name
                else name ^ "#" ^ Int.toString( ! uid )

fun foldsep sep [] = ""
 |  foldsep sep (s::ss) = s ^ sep ^ (foldsep sep ss)

fun printInst (LABEL(sym)) = (printSym sym) ^ ":"
 |  printInst (MOVE(t1, t2)) =       "  move " ^ (printTree t1) ^ " " ^ (printTree t2) ^ ""
 |  printInst (CALL(f, ret, args)) = "  call " ^ (printSym ret) ^ " = " ^ (printSym f) ^ " " ^ (foldsep " " (map printTree args)) ^ ""
 |  printInst (RET(t)) =             "  ret  " ^ (printTree t) ^ ""
 |  printInst (JUMP(label)) =        "  jump " ^ (printSym label) ^ ""
 |  printInst (CJUMP(comp, t1, t2, label)) = 
         "  cmp  " ^ (printTree t1) ^ " " ^ (printCmpOp comp) ^ " " ^ (printTree t2) ^ "  jump " ^ (printSym label) ^ ""

and printTree (IMM(i)) = "$" ^ Int.toString(i)
 |  printTree (OFFSET(field)) = "(dot " ^ (printSym field) ^ ")"
 |  printTree (STRING(s)) = "\"" ^ s ^ "\""
 |  printTree (MEM(t)) = "(mem " ^ (printTree t) ^ ")"
 |  printTree (VAR(sym)) = printSym sym
 |  printTree (BINOP(bop, t1, t2)) = "(" ^ (printBinOp bop) ^ " " ^ (printTree t1) ^ " " ^ (printTree t2) ^ ")"
 |  printTree (EMPTY) = ""

and printBinOp (PLUS) = "+"
 |  printBinOp (MINUS) = "-"
 |  printBinOp (TIMES) = "*"
 |  printBinOp (DIV) = "/"

and printCmpOp (EQ) = "eq"
 |  printCmpOp (NEQ) = "neq"
 |  printCmpOp (LT) = "<"
 |  printCmpOp (LE) = "<="
 |  printCmpOp (GT) = ">"
 |  printCmpOp (GE) = ">="

fun printFun(FUN{ fundecl = fundecl, impl = ins }) =
    let val ins_str = foldsep "\n" (map printInst ins)
    in
        case fundecl of
          (A.FUNDECL(sym, args, ty, body)) => "------------------------------\n" ^ "FUNCTION " ^ (printSym sym) ^ "\n" ^ ins_str
        | _ => raise SemanticError("Function represented by non-fundecl")
    end

fun printProgram funs = 
    let
        val prog_str = foldr op^ "" (map printFun funs)
    in 
        (print prog_str)
    end

end
