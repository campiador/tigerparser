structure X64 =
struct

structure A = AST
exception InternalError of string
exception SemanticError of string
exception NotImplemented

(* Registers
   At this stage we have two kinds of registers: hardware and virtual. Hardware registers
   refer to actual registers, which is often necessary for particular instructions and
   calling conventions. Virtual registers represent operands that must be in *some*
   register, but not any particular one.
*)

datatype register = HARDWARE of string * int
                  | VIRTUAL of A.symbol

(* Hardware registers
   The string just makes it easy to print the name.
*)

val Rax = HARDWARE("rax", 0)
val Rcx = HARDWARE("rcx", 1)
val Rdx = HARDWARE("rdx", 2)
val Rbx = HARDWARE("rbx", 3)
val Rsi = HARDWARE("rsi", 4)
val Rdi = HARDWARE("rdi", 5)
val Rsp = HARDWARE("rsp", 6)
val Rbp = HARDWARE("rbp", 7)
val R8  = HARDWARE("r8", 8)
val R9  = HARDWARE("r9", 9)
val R10 = HARDWARE("r10", 10)
val R11 = HARDWARE("r11", 11)
val R12 = HARDWARE("r12", 12)
val R13 = HARDWARE("r13", 13)
val R14 = HARDWARE("r14", 14)
val R15 = HARDWARE("r15", 15)

(* Operands
   Operands support various addressing modes, which are shown X64 assembly form
   in comments. The VAR form represents a program variable whose storage has
   not yet been determined. The register allocator will figure this out. *)

datatype operand = IMM of int                            (*   $53             *)
                 | DATA of string
                 | VAR of A.symbol                       (*  Unallocated variable *)
                 | DIRECT of register                    (*   %r12            *)
                 | INDIRECT of register                  (*   (%rax)          *)
                 | OFFSET of int * register              (*   -16(%rbp)       *)
                 | SCALED of register * register * int   (*   (%rax, %rcx, 8) *)

(* Instructions
   Each instruction takes one or two operands. See the X64 cheat sheet for
   specific details on the role of each operand. Remember that the first
   operand is the *source* and the second operand is the *destination*. *)

datatype x64ins = MOVE of operand * operand
             | PUSH of operand
             | POP of operand
             | INC of operand
             | DEC of operand
             | NEG of operand
             | NOT of operand
             | LEA of operand * operand
             | ADD of operand * operand
             | SUB of operand * operand
             | IMUL of operand * operand
             | IDIV of operand * operand
             | XOR of operand * operand
             | OR  of operand * operand
             | AND of operand * operand
             | SHL of operand * operand
             | SHR of operand * operand
             | SAR of operand * operand
             | CMP of operand * operand
             | TEST of operand * operand
             | JMP of A.symbol
             | JE of A.symbol
             | JNE of A.symbol
             | JG of A.symbol
             | JGE of A.symbol
             | JL of A.symbol
             | JLE of A.symbol
             | LABEL of A.symbol
             | CALL of A.symbol
             | LEAVE
             | RET
             | COMMENT of string (* x64 Comment for debugging *)

(* X64 Function
   We wrap the MIR function representation together with the list of
   generated X64 instructions. *)

datatype x64fun = FUN of { mirfun: MIR.funrep, impl: x64ins list }

(* ---------------------------------------------------------------------
   Code generator 

   Here's the code that translates a list of MIR instructions into a
   list of X64 instructions. There are three functions: generateIns,
   generateOperand, and generateRegister. In all three cases, the
   input to the function is a fragment of MIR -- a "tile" -- for which
   we will generate X64 constructs. 

   The key idea here is that both generateOperand and generateRegister
   operate on MIR trees, but they produce a different kind of result:

   generateRegister takes a register as an argument, and generates a 
   list of X64 instructions that leave the result in that register. 

   generateOperand generates an operand, which is not necessarily a
   register, along with the list of instructions. This function allows
   us to look for tiles that match addressing modes, such as indirect
   with offset and scaled.
*)

fun generateIns (MIR.LABEL(l)) = [ LABEL(l) ]
 |  generateIns (MIR.MOVE(_, MIR.EMPTY)) = []   (* Needed in some cases; don't ask *)
 |  generateIns (MIR.MOVE(t1, t2)) = 
    let val (t1op, t1ins) = generateOperand t1
        val (t2op, t2ins) = generateOperand t2
    in
        t2ins @ t1ins @ [ MOVE(t2op, t1op) ]
    end

 |  generateIns (MIR.CALL(f, ret, args)) =
    let
    fun passArgs([t1]) = (* TODO: more than 1 variable *)
	let
	    val (t1op, t1ins) = generateOperand t1
	in
	    t1ins @ [MOVE(t1op, DIRECT(Rdi))] (*FIXME: should I allocate Rdi using generate register? *)
	end
      | passArgs[t1, t2] = 
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @generateRegister(t2, Rsi)
	end
      | passArgs[t1, t2, t3] =
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	    val (t3op, t3ins) = generateOperand t3
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @ generateRegister(t2, Rsi) @ t3ins @ generateRegister(t3, Rdx)
	end
      | passArgs[t1, t2, t3, t4] =
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	    val (t3op, t3ins) = generateOperand t3
	    val (t4op, t4ins) = generateOperand t4
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @ generateRegister(t2, Rsi) @ t3ins @ generateRegister(t3, Rdx) @ t4ins @ generateRegister(t4, Rcx)
	end
      | passArgs[t1, t2, t3, t4, t5] =
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	    val (t3op, t3ins) = generateOperand t3
	    val (t4op, t4ins) = generateOperand t4
	    val (t5op, t5ins) = generateOperand t5
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @ generateRegister(t2, Rsi) @ t3ins @ generateRegister(t3, Rdx) @ t4ins @ generateRegister(t4, Rcx) @ t5ins @ generateRegister(t5, R8)
	end
      | passArgs[t1, t2, t3, t4, t5, t6] =
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	    val (t3op, t3ins) = generateOperand t3
	    val (t4op, t4ins) = generateOperand t4
	    val (t5op, t5ins) = generateOperand t5
	    val (t6op, t6ins) = generateOperand t6
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @ generateRegister(t2, Rsi) @ t3ins @ generateRegister(t3, Rdx) @ t4ins @ generateRegister(t4, Rcx) @ t5ins @ generateRegister(t5, R8) @ t6ins @ generateRegister(t6, R9)
	end
      | passArgs(t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: other_args) =
	let
	    val (t1op, t1ins) = generateOperand t1
	    val (t2op, t2ins) = generateOperand t2
	    val (t3op, t3ins) = generateOperand t3
	    val (t4op, t4ins) = generateOperand t4
	    val (t5op, t5ins) = generateOperand t5
	    val (t6op, t6ins) = generateOperand t6

	    fun pushList([]) = []
	      |	pushList([one_arg]) = 
		let
		    val (t1op, t1ins) = generateOperand one_arg
		    val push_ins = PUSH(t1op)
		in
		    t1ins @ [push_ins]
		end
	      | pushList(head::tail) = pushList([head]) @ pushList(tail)
 
	    val push_insts   = pushList(other_args)
	in
	    t1ins @  generateRegister(t1, Rdi) @ t2ins @ generateRegister(t2, Rsi) @ t3ins @ generateRegister(t3, Rdx) @ t4ins @ generateRegister(t4, Rcx) @ t5ins @ generateRegister(t5, R8) @ t6ins @ generateRegister(t6, R9) @ push_insts
	end

    val returnVarTree = MIR.VAR(ret)
    val returnMemTree = MIR.MEM(returnVarTree)
    val (retOp, retIns) = generateOperand returnMemTree (*TODO: loading address; should it be only returnVarTree? *)

    in
	passArgs(args) @ retIns @ [CALL(f)]
    end
 |  generateIns (MIR.RET(r)) =  
    let
	val(rop, rins) = generateOperand r (*TODO: figure out what to do with rop*)
    in
	rins @ [RET]
    end
 |  generateIns (MIR.JUMP(l)) = [ JMP(l) ]
 |  generateIns (MIR.CJUMP(cmpop, t1, t2, l)) =
    let
	val (t1op, t1ins) = generateOperand t1
        val (t2op, t2ins) = generateOperand t2
	val comp_ins = CMP(t2op, t1op)
	fun true_jump compare_operator =
	    case compare_operator of
	        MIR.EQ  => JE  l
	      | MIR.NEQ => JNE l      
	      | MIR.LT  => JL  l
	      | MIR.GE  => JGE l
	      | MIR.LE  => JLE l
	      | MIR.GT  => JG  l
	val cjump_ins = [comp_ins] @ [true_jump(cmpop)]
    in
	cjump_ins
    end

and generateOperand (MIR.IMM(i)) = (IMM(i), [])
 |  generateOperand (MIR.OFFSET(field)) = (OFFSET(8, VIRTUAL(field)), []) (* FIXME: calculate OFFSET *)
 |  generateOperand (MIR.STRING(s)) = (DATA(s), [])
 |  generateOperand (MIR.MEM(MIR.VAR(t_symbol))) =
    let
	val the_register = VIRTUAL(t_symbol) (* dafuq did I type here? *)
	val operand = INDIRECT(the_register)
	val ins = [] (*FXIME: because the symbol does not need any instructions, but I'm sure if I change the VIRTUAL I need to run some instructions here*) 
    in
	(operand , ins)
    end
    
 |  generateOperand (MIR.MEM(t)) = (IMM(0), []) (*FIXME: please!*)
 |  generateOperand (MIR.VAR(s)) = (VAR(s), [])
 |  generateOperand (MIR.BINOP(binop, t1, t2)) =
    let
	val (t1op, t1ins) = generateOperand t1
        val (t2op, t2ins) = generateOperand t2

	fun mir2x64_binop_ins (operator, t1operand, t2operand) =
	    case operator of 
	        MIR.PLUS  => ADD (t2operand, t1operand)
	      | MIR.MINUS => SUB (t2operand, t1operand)
	      | MIR.TIMES => IMUL(t2operand, t1operand)
	      | MIR.DIV   => IDIV(t2operand, t1operand)

	val binop_ins = mir2x64_binop_ins(binop, t2op, t1op)
    in
	(t2op, t1ins @ t2ins @ [binop_ins])
    end

 |  generateOperand (MIR.EMPTY) = (IMM(0), []) (*FIXME: returning zero?*)

and generateRegister (MIR.IMM(i), reg) = [MOVE(IMM(i), DIRECT(reg))]
 |  generateRegister (MIR.OFFSET(field), reg) = raise InternalError "No register representation for OFFSET"
 |  generateRegister (MIR.STRING(s), reg) = [ MOVE(DATA(s), DIRECT(reg)) ]
 |  generateRegister (MIR.MEM(t), reg) = raise InternalError "No register representation for MEM"
 |  generateRegister (MIR.VAR(s), reg) = [ MOVE( VAR(s), DIRECT(reg) ) ]
 |  generateRegister (MIR.BINOP(binop, t1, t2), reg) = raise NotImplemented
 |  generateRegister (MIR.EMPTY, reg) = raise InternalError "Generate called on empty expression"

and generateFun (mirfun as MIR.FUN{ fundecl = fundecl, impl = ins }) =
    let val x64ins = foldr op@ [] (map generateIns ins)
    in
        FUN{ mirfun = mirfun, impl = x64ins }
    end

and generateProgram funs = map generateFun funs

(* --------------------------------------------------------------------- *)

(* Emit assembly

   Generates the text representation of the code suitable for the GCC assembler.
   The entry point is programString, which takes a list of X64 functions and
   returns a single string with the complete assembly representation ready to
   send to gcc.   
 *)

fun printSym (name, pos, line, uid) = 
    if !uid = 0 then name
                else name ^ "_" ^ Int.toString( ! uid )

fun regString (HARDWARE(nm, i)) = "%" ^ nm
 |  regString(VIRTUAL(s)) = "%" ^ (printSym s)

fun intString i = if i < 0 then "-" ^ (Int.toString (~ i))
                           else (Int.toString i)

fun operandString (IMM(i)) = "$" ^ intString i
 |  operandString (DATA(s)) = "\"" ^ s ^ "\""
 |  operandString (VAR(s)) = printSym s
 |  operandString (DIRECT(r)) = regString r
 |  operandString (INDIRECT(r)) = "(" ^ (regString r) ^ ")"
 |  operandString (OFFSET(off, r)) = (intString off) ^ "(" ^ (regString r) ^ ")"
 |  operandString (SCALED(b,off,sc)) = "(" ^ (regString b) ^ ", " ^ (regString off) ^ ", " ^ (intString sc) ^ ")"

fun insString1 s op1     = "  " ^ s ^ "     " ^ (operandString op1)
fun insString2 s op1 op2 = "  " ^ s ^ "     " ^ (operandString op1) ^ ", " ^ (operandString op2)

fun insString (MOVE (s, d)) = insString2 "movq " s d
  | insString (PUSH s)      = insString1 "pushq" s
  | insString (POP s)       = insString1 "popq " s
  | insString (INC s)       = insString1 "incq " s
  | insString (DEC s)       = insString1 "decq " s
  | insString (NEG s)       = insString1 "negq " s
  | insString (NOT s)       = insString1 "notq " s
  | insString (LEA (s, d))  = insString2 "leaq  " s d
  | insString (ADD (s, d))  = insString2 "addq " s d
  | insString (SUB (s, d))  = insString2 "subq " s d
  | insString (IMUL (s, d)) = insString2 "imulq" s d
  | insString (IDIV (s, d)) = insString2 "idivq" s d
  | insString (XOR (s, d))  = insString2 "xorq " s d
  | insString (OR  (s, d))  = insString2 "orq  " s d
  | insString (AND (s, d))  = insString2 "andq " s d
  | insString (SHL (s, d))  = insString2 "shlq " s d
  | insString (SHR (s, d))  = insString2 "shrq " s d
  | insString (SAR (s, d))  = insString2 "sarq " s d
  | insString (CMP (s, d))  = insString2 "cmpq " s d
  | insString (TEST (s, d)) = insString2 "testq" s d
  | insString (JMP l)       = "  jmp " ^ (printSym l)
  | insString (JE l)        = "  je  " ^ (printSym l)
  | insString (JNE l)       = "  jne " ^ (printSym l)
  | insString (JG l)        = "  jg  " ^ (printSym l)
  | insString (JGE l)       = "  jge " ^ (printSym l)
  | insString (JL l)        = "  jl  " ^ (printSym l)
  | insString (JLE l)       = "  jle " ^ (printSym l)
  | insString (LABEL l)     = (printSym l) ^ ":"
  | insString (CALL f)      = "  call  " ^ (printSym f)
  | insString LEAVE         = "leaveq"
  | insString RET           = "ret"
  | insString (COMMENT s)   = "  % " ^ s

fun funcString (FUN{ mirfun=MIR.FUN{ fundecl = fundecl, impl = _}, impl=x64ins}) =
    let val assembly = MIR.foldsep "\n" (map insString x64ins)
    in 
        case fundecl of
          (A.FUNDECL(name, args, ty, body)) =>  
              ".globl " ^ (printSym name) ^ "\n" ^
              ".type     " ^ (printSym name) ^ ", @function\n"  ^
              assembly ^ "\n"

        | _ => raise SemanticError("Function represented by non-fundecl")
    end

fun programString funcs = foldr op^ "" (map funcString funcs)

end