datatype instr = INT of int | STR of string | NAM of string | BOOL of bool | ERROR | UNIT
datatype comm = PUSH of instr | ADD | SUB | POP | SWAP | NEG | TRU | QUI | FAL | ERR | DIV | REM | MUL | AND | OR | NOT | EQUAL | LESS | BIND | IF | LET  | END

fun lookup(NAM v1,e1::env,lstack,ends) = case e1 of (NAM v2,INT v3)::t => if NAM v1 = NAM v2 then INT v3 else lookup(NAM v1,env,lstack,ends)
    |lookup(NAM v1,(NAM v2,STR v3)::env,lstack,ends) = if NAM v1 = NAM v2 then STR v3 else lookup(NAM v1,env,lstack,ends) 
    |lookup(NAM v1,(NAM v2,BOOL v3)::env,lstack,ends) = if NAM v1 = NAM v2 then BOOL v3 else lookup(NAM v1,env,lstack,ends)
	|lookup(NAM v1,(NAM v2,UNIT)::env,lstack,ends) = if NAM v1 = NAM v2 then UNIT else lookup(NAM v1,env,lstack,ends)
	|lookup(NAM v1,[],lstack,ends) = NAM v1
	
fun checknm L = case L of (h::t) => Char.isAlpha h
	
fun remqu (#"\""::l1,l2) = remqu(l1,l2)
	|remqu (v1::l1,l2) = remqu(l1,l2@[v1])
	|remqu ([],l2) = implode(l2)

fun interpreter(infile : string, outfile : string) =
let
	val instream = TextIO.openIn infile
	val reading = TextIO.inputLine instream
	val outstream = TextIO.openOut outfile
	fun helper(reading : string option , L) =
	   case reading of 
		NONE => (L)
	      | SOME(c) => case String.tokens Char.isSpace c of
						["add"] => helper(TextIO.inputLine instream,L@[ADD])
						| ["sub"] => helper(TextIO.inputLine instream,L@[SUB])
						| ["pop"] => helper(TextIO.inputLine instream,L@[POP])
						| ["swap"] => helper(TextIO.inputLine instream,L@[SWAP])
						| ["rem"] => helper(TextIO.inputLine instream,L@[REM])
						| ["div"] => helper(TextIO.inputLine instream,L@[DIV])
						| ["mul"] => helper(TextIO.inputLine instream,L@[MUL])
						| ["let"] => helper(TextIO.inputLine instream,L@[LET])
						| ["end"] => helper(TextIO.inputLine instream,L@[END])
						| ["and"] => helper(TextIO.inputLine instream,L@[AND])
						| ["or"] => helper(TextIO.inputLine instream,L@[OR])
                        | ["not"] => helper(TextIO.inputLine instream,L@[NOT])
						| [":error:"] => helper(TextIO.inputLine instream,L@[ERR])
						| ["if"] => helper(TextIO.inputLine instream,L@[IF])
						| [":true:"] => helper(TextIO.inputLine instream,L@[TRU])
						| [":false:"] => helper(TextIO.inputLine instream,L@[FAL])
						| ["quit"] => helper(TextIO.inputLine instream,L@[QUI])
						| ["lessThan"] => helper(TextIO.inputLine instream,L@[LESS])
						| ["equal"] => helper(TextIO.inputLine instream,L@[EQUAL])
						| ["neg"] => helper(TextIO.inputLine instream,L@[NEG])
						| ["bind"] => helper(TextIO.inputLine instream,L@[BIND])
	                    | ["push", v] => if String.isSubstring "." v = false then(case Int.fromString v of 
						     SOME (h) => helper(TextIO.inputLine instream,L@[PUSH(INT h)])
						     | NONE => if String.isPrefix "\"" v = true then helper(TextIO.inputLine instream,L@[PUSH(STR (remqu(explode(v),[])))])
									else if checknm (explode(v)) = true then helper(TextIO.inputLine instream,L@[PUSH(NAM v)])
					                     else  helper(TextIO.inputLine instream,L@[ERR]))
										 else helper(TextIO.inputLine instream,L@[ERR])
	                    | ["push",v,s] => if String.isPrefix "\"" v = true then helper(TextIO.inputLine instream,L@[PUSH(STR (remqu(explode(v^" "^s),[])))])
											else helper(TextIO.inputLine instream,L@[ERR])
						| ["push",v,s,k] => if String.isPrefix "\"" v = true then helper(TextIO.inputLine instream,L@[PUSH(STR (remqu(explode(v^" "^s^" "^k),[])))])
											else helper(TextIO.inputLine instream,L@[ERR])
						| ["push",v,s,k,l] => if String.isPrefix "\"" v = true then helper(TextIO.inputLine instream,L@[PUSH(STR (remqu(explode(v^" "^s^" "^k^" "^l),[])))])
											else helper(TextIO.inputLine instream,L@[ERR])
										  
										  
	
	fun process (PUSH(INT v)::cl, vl, env,l1::lstack,ends) =if ends = 0 then process(cl,INT v::vl, env,l1::lstack,ends) else process(cl,vl,env,(INT v::l1)::lstack,ends)
		|process (PUSH(STR v)::cl, vl, env,l1::lstack,ends) = if ends = 0 then process(cl,STR v::vl, env,l1::lstack,ends) else process(cl,vl,env,(STR v::l1)::lstack,ends)
		|process (PUSH(NAM v)::cl, vl, env,l1::lstack,ends) = if ends = 0 then process(cl,NAM v::vl, env,l1::lstack,ends) else process(cl,vl,env,(NAM v::l1)::lstack,ends)
		|process (ADD::cl, INT v1::INT v2::vl, env,lstack,0) = process(cl,INT (v1+v2)::vl, env,lstack,0)
			
		|process (ADD::cl, NAM v1::INT v2::vl, env,lstack,0) = (case lookup(NAM v1,env,lstack,0) of INT v3 => process(cl,INT (v3+v2)::vl,env,lstack,0)
																				| _ => process(cl,ERROR::NAM v1::INT v2::vl,env,lstack,0) )
		
		|process (ADD::cl, INT v2::NAM v1::vl, env,lstack,0) = (case lookup(NAM v1,env,lstack,0) of INT v3 => process(cl,INT (v3+v2)::vl,env,lstack,0)
																				| _ => process(cl,ERROR::INT v2::NAM v1::vl,env,lstack,0) )
		
		|process (ADD::cl, NAM v1::NAM v2::vl, env,lstack,0) = (case lookup(NAM v1,env,lstack,0) of INT v3 => (case lookup(NAM v2,env,lstack,0) of INT v4 => process(cl,INT (v3+v4)::vl,env,lstack,0)
																							| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,0) )
																				| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,0) )
		
		
		|process (ADD::cl, vl, env,l1::lstack,ends) = (case l1 of NAM v1::INT v2::t => (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,vl,env,(INT (v3+v2)::l1)::lstack,ends)
																				| _ => process(cl,vl,env,(ERROR::NAM v1::INT v2::l1)::lstack,ends) )
																| INT v2::NAM v1::t => (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,vl,env,(INT (v3+v2)::l1)::lstack,ends)
																				| _ => process(cl,vl,env,(ERROR::INT v2::NAM v1::l1)::lstack,ends) )
																| INT h1::INT h2::t => process(cl,vl, env,(INT (h1+h2)::l1)::lstack,ends)
		
																| NAM v1::NAM v2::t => (case lookup(NAM v1,env,lstack,ends) of INT v3 => (case lookup(NAM v2,env,lstack,ends) of INT v4 => process(cl,vl,env,(INT (v3+v4)::l1)::lstack,ends)
																							| _ => process(cl,vl,env,(ERROR::NAM v1::NAM v2::l1)::lstack,ends) )
																				        | _ => process(cl,vl,env,(ERROR::NAM v1::NAM v2::l1)::lstack,ends) )
																| _ => process(cl,vl,env,(ERROR::l1)::lstack,ends)	)
		 
																
		|process (SUB::cl, INT v1::INT v2::vl, env,lstack,ends) = process(cl,INT (v2-v1)::vl, env,lstack,ends)
		
		|process (SUB::cl, NAM v1::INT v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT (v2-v3)::vl, env,lstack,ends)
														| _ => process (cl,ERROR::NAM v1::INT v2::vl,env,lstack,ends))
		
		|process (SUB::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => (case lookup(NAM v2,env,lstack,ends) of INT v4 => process(cl,INT (v4-v3)::vl,env,lstack,ends)
																							| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
																				| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
		|process (SUB::cl, INT v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v2,env,lstack,ends) of INT v3 => process(cl,INT (v3-v1)::vl, env,lstack,ends)
														| _ => process (cl,ERROR::INT v1::NAM v2::vl,env,lstack,ends))
														
		|process (DIV::cl, INT v1::INT v2::vl, env,lstack,ends) = if v1=0 then process(cl,ERROR::INT v1::INT v2::vl, env,lstack,ends) 
													else process(cl,INT (v2 div v1)::vl, env,lstack,ends)
													
		|process (DIV::cl, NAM v1::INT v2::vl, env,lstack,ends) =  (case lookup(NAM v1,env,lstack,ends) of INT v3 => if v3=0 then process(cl,ERROR::NAM v1::INT v2::vl, env,lstack,ends) 
													                                                  else process(cl,INT (v2 div v3)::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::NAM v1::INT v2::vl, env,lstack,ends) )
		
		|process (DIV::cl, INT v1::NAM v2::vl, env,lstack,ends) =  (case lookup(NAM v2,env,lstack,ends) of INT v3 => if v1=0 then process(cl,ERROR::INT v1::NAM v2::vl, env,lstack,ends) 
													                                                  else process(cl,INT (v3 div v1)::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::INT v1::NAM v2::vl, env,lstack,ends) )
	    
		|process (DIV::cl, NAM v1::NAM v2::vl, env,lstack,ends) =  (case lookup(NAM v1,env,lstack,ends) of INT v3 => if v3=0 then process(cl,ERROR::NAM v1::NAM v2::vl, env,lstack,ends) 
													                                              else ( case lookup(NAM v2,env,lstack,ends) of 
																								         INT v4 => process(cl,INT (v4 div v3)::vl, env,lstack,ends)
																										 | _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends)) 
																					| _ => process(cl,ERROR::NAM v1::NAM v2::vl, env,lstack,ends) )
													
		|process (EQUAL::cl, INT v1::INT v2::vl, env,lstack,ends) = if v1=v2 then process(cl,BOOL true::vl, env,lstack,ends)
														else process(cl,BOOL false::vl, env,lstack,ends)
														
		|process (EQUAL::cl, NAM v1::INT v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => if v2=v3 then process(cl,BOOL true::vl, env,lstack,ends)
														                                      else process(cl,BOOL false::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::NAM v1::INT v2::vl,env,lstack,ends) )
		
		|process (EQUAL::cl, INT v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v2,env,lstack,ends) of INT v3 => if v1=v3 then process(cl,BOOL true::vl, env,lstack,ends)
														                                      else process(cl,BOOL false::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::INT v1::NAM v2::vl,env,lstack,ends) )
																					
		|process (EQUAL::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => ( case lookup(NAM v2,env,lstack,ends) of 
																										INT v4 => if v4=v3 then process(cl,BOOL true::vl, env,lstack,ends)
														                                                          else process(cl,BOOL false::vl, env,lstack,ends)
																										| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) ) 
																					| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
		
		|process (LESS::cl, INT v1::INT v2::vl, env,lstack,ends) = if v2<v1 then process(cl,BOOL true::vl, env,lstack,ends)
														else process(cl,BOOL false::vl, env,lstack,ends)
														
		|process (LESS::cl, NAM v1::INT v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => if v2<v3 then process(cl,BOOL true::vl, env,lstack,ends)
														                                      else process(cl,BOOL false::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::NAM v1::INT v2::vl,env,lstack,ends) )
		
		|process (LESS::cl, INT v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v2,env,lstack,ends) of INT v3 => if v3<v1 then process(cl,BOOL true::vl, env,lstack,ends)
														                                      else process(cl,BOOL false::vl, env,lstack,ends) 
																					| _ => process(cl,ERROR::INT v1::NAM v2::vl,env,lstack,ends) )
		
		|process (LESS::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => ( case lookup(NAM v2,env,lstack,ends) of 
																										INT v4 => if v4<v3 then process(cl,BOOL true::vl, env,lstack,ends)
														                                                          else process(cl,BOOL false::vl, env,lstack,ends)
																										| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) ) 
																					| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
		|process (NOT::cl, BOOL v1::vl, env,lstack,ends) = process(cl,BOOL (not v1)::vl, env,lstack,ends)
		
		|process (NOT::cl, NAM v1::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of BOOL v3 => process(cl,BOOL (not v3)::vl, env,lstack,ends) 
																		| _ => process(cl,ERROR::NAM v1::vl,env,lstack,ends))
   			
		|process (AND::cl, BOOL v1::BOOL v2::vl, env,lstack,ends) = process(cl,BOOL (v1 andalso v2)::vl, env,lstack,ends)
		
		|process (AND::cl, NAM v1::BOOL v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of BOOL v3 => process(cl,BOOL (v3 andalso v2)::vl,env,lstack,ends) 
																					| _ => process(cl,ERROR::NAM v1::BOOL v2::vl,env,lstack,ends) )
		
		|process (AND::cl, BOOL v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v2,env,lstack,ends) of BOOL v3 => process(cl,BOOL (v1 andalso v3)::vl,env,lstack,ends) 
																					| _ => process(cl,ERROR::BOOL v1::NAM v2::vl,env,lstack,ends) )
    	
		|process (AND::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of BOOL v3 => ( case lookup(NAM v2,env,lstack,ends) of 
																										BOOL v4 => process(cl,BOOL (v3 andalso v4)::vl,env,lstack,ends)
																										| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) ) 
																					| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
																					
		|process (OR::cl, BOOL v1::BOOL v2::vl, env,lstack,ends) = process(cl,BOOL (v1 orelse v2)::vl, env,lstack,ends)
		
		|process (OR::cl, NAM v1::BOOL v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of BOOL v3 => process(cl,BOOL (v3 orelse v2)::vl,env,lstack,ends) 
																					| _ => process(cl,ERROR::NAM v1::BOOL v2::vl,env,lstack,ends) )
		
		|process (OR::cl, BOOL v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v2,env,lstack,ends) of BOOL v3 => process(cl,BOOL (v1 orelse v3)::vl,env,lstack,ends) 
																					| _ => process(cl,ERROR::BOOL v1::NAM v2::vl,env,lstack,ends) )
		
		|process (OR::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of BOOL v3 => ( case lookup(NAM v2,env,lstack,ends) of 
																										BOOL v4 => process(cl,BOOL (v3 orelse v4)::vl,env,lstack,ends)
																										| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) ) 
																					| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )																			
		|process (MUL::cl, INT v1::INT v2::vl, env,lstack,ends) = process(cl,INT (v1*v2)::vl, env,lstack,ends)
		
		|process (MUL::cl, NAM v1::INT v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT (v3*v2)::vl,env,lstack,ends)
																				| _ => process(cl,ERROR::NAM v1::INT v2::vl,env,lstack,ends) )
																				
		|process (MUL::cl, INT v2::NAM v1::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT (v3*v2)::vl,env,lstack,ends)
																				| _ => process(cl,ERROR::INT v2::NAM v1::vl,env,lstack,ends) )
        
        |process (MUL::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => (case lookup(NAM v2,env,lstack,ends) of INT v4 => process(cl,INT (v3*v4)::vl,env,lstack,ends)
																							| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
																				| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )		
																				
		|process (REM::cl, INT v1::INT v2::vl, env,lstack,ends) = process(cl,INT (v2 mod v1)::vl, env,lstack,ends)
		
		|process (REM::cl, NAM v1::INT v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT (v2 mod v3)::vl,env,lstack,ends)
																				| _ => process(cl,ERROR::NAM v1::INT v2::vl,env,lstack,ends) )
																				
		|process (REM::cl, INT v2::NAM v1::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT (v3 mod v2)::vl,env,lstack,ends)
																				| _ => process(cl,ERROR::INT v2::NAM v1::vl,env,lstack,ends) )
	    
		|process (REM::cl, NAM v1::NAM v2::vl, env,lstack,ends) = (case lookup(NAM v1,env,lstack,ends) of INT v3 => (case lookup(NAM v2,env,lstack,ends) of INT v4 => process(cl,INT (v4 mod v3)::vl,env,lstack,ends)
																							| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
																				| _ => process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,ends) )
																				
		|process (NEG::cl, INT v1::vl, env,lstack,ends) = process(cl,INT(~v1)::vl, env,lstack,ends)
		|process (NEG::cl, NAM v1::vl, env,lstack,ends) =(case lookup(NAM v1,env,lstack,ends) of INT v3 => process(cl,INT(~v3)::vl, env,lstack,ends) 
																		| _ => process(cl,ERROR::NAM v1::vl,env,lstack,ends))
		|process (SWAP::cl, v1::v2::vl, env,lstack,ends) = process(cl,v2::v1::vl, env,lstack,ends)
		|process (POP::cl, v1::vl, env,lstack,ends) = process(cl,vl, env,lstack,ends)
		|process (TRU::cl, vl, env,lstack,ends) = process(cl,BOOL true::vl, env,lstack,ends)
		|process (FAL::cl, vl, env,lstack,ends) = process(cl,BOOL false::vl, env,lstack,ends)
		|process (BIND::cl, INT v1::NAM v2::vl, e1::env,lstack,0) = process(cl,UNIT::vl,((NAM v2,INT v1)::e1)::env,lstack,0)
		|process (BIND::cl, STR v1::NAM v2::vl, e1::env,lstack,0) = process(cl,UNIT::vl,((NAM v2,STR v1)::e1)::env,lstack,0)
		|process (BIND::cl, BOOL v1::NAM v2::vl, e1::env,lstack,0) = process(cl,UNIT::vl,((NAM v2,BOOL v1)::e1)::env,lstack,0)
		|process (BIND::cl, UNIT::NAM v2::vl, e1::env,lstack,0) = process(cl,UNIT::vl,((NAM v2,UNIT)::e1)::env,lstack,0)
		|process (BIND::cl, NAM v1::NAM v2::vl, e1::env,lstack,0) = if lookup(NAM v1,env,lstack,0)=NAM v1 then process(cl,ERROR::NAM v1::NAM v2::vl,env,lstack,0)
															else process(cl,UNIT::vl,((NAM v2,(lookup(NAM v1,env,lstack,0)))::e1)::env,lstack,0)
															
		|process (BIND::cl, vl,e1::env,l1::lstack,ends) = if ends <> 0 then (case l1 of INT v1::NAM v2::t => process(cl,vl,(NAM v2,INT v1)::env,(UNIT::l1)::lstack,ends)
																| STR v1::NAM v2::t	=> process(cl,vl,(NAM v2,STR v1)::env,(UNIT::l1)::lstack,ends))
														else process(cl,ERROR::vl,env,l1::lstack,ends)  
		
		|process (IF::cl, v1::v2::BOOL v3::vl, env,lstack,ends) = if v3 = true then process(cl,v1::vl,env,lstack,ends) else process(cl,v2::vl,env,lstack,ends)
		|process (LET::cl, vl, env,lstack,ends) = if ends=0 then process(cl,vl,env,lstack,ends+1) else process(cl,vl,env,[]::lstack,ends+1)
		|process (END::cl, vl, env,v1::lstack,1) = (case v1 of h::t => process(cl,h::vl,env,[]::lstack,0))
		|process (END::cl, vl, env,v1::v2::lstack,ends) = (case v1 of h::t => process(cl,vl,env,(h::v2)::lstack,ends-1))
		|process (QUI::cl, vl, env,lstack,ends) = process(cl,vl, env,lstack,ends)
		|process (_::cl, vl, env,lstack,ends) = process(cl,ERROR::vl, env,lstack,ends)
		|process ([],vl, env,lstack,ends) = vl
		
		  
	fun display (INT v::L) = if Int.sameSign(v,~1) = false then (TextIO.output(outstream,(Int.toString v) ^ "\r\n"); display L)
							else (TextIO.output(outstream,("-" ^ Int.toString (abs v)) ^ "\r\n"); display L)
	 | display (UNIT::L) = (TextIO.output(outstream,":unit:\r\n"); display L)
     | display (NAM v::L) = (TextIO.output(outstream,v ^ "\r\n"); display L)
	 | display (STR v::L) = (TextIO.output(outstream,v ^ "\r\n"); display L)
	 | display (ERROR::L) = (TextIO.output(outstream,":error:\r\n"); display L)
	 | display (BOOL true::L) = (TextIO.output(outstream,":true:\r\n"); display L)
	 | display (BOOL false::L) = (TextIO.output(outstream,":false:\r\n"); display L)
	 | display [] = (TextIO.closeIn instream; TextIO.closeOut outstream)
in
display(process(helper(reading,[]),[],[[]],[[]],0))
end

val _ = interpreter("sample.txt","output.txt");





