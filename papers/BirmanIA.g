# General things for working in the free group on $S_K\cup S_Q$.
fg := FreeGroup( "xa", "xb", "xc", "xd", "xe", "xf", "xg", "y");  #We use this "fg" as the free group $F_{n+1}$.  $S_A$, $S_Q$ and $S_K$ generators take parameters in these generators.
AssignGeneratorVariables(fg);				#This creates global variables "xa", ... , "xf", "y" that represent the corresponding generators of fg.
invertmove := function(mov)				#takes in a generator from $S_Q$ or $S_K$, represented as a list, and returns its inverse
	if not IsList(mov) then return; fi;		#quit if not given a list as input
	if mov[1]="M" or mov[1]="C" then		
		return [mov[1],mov[2],Inverse(mov[3])];	#invert "M" or "C" move by inverting last parameter
	elif mov[1]="Mc" then
		return [mov[1],mov[2],mov[4],mov[3]];	#invert commutator transvection by swapping order of last two parameters
	elif mov[1]="I" or mov[1]="P" then
		return mov;
	fi;
end;
iw := function(list)					#takes a word in $S_Q$ and $S_K$ generators and returns its inverse
	local out;
	out := Reversed(list);
	Apply(out, invertmove);
	return out;
end;

freereducemovelist :=function(movelist)			#Takes in a word in $S_Q$ and $S_K$ generators and returns the freely reduced form of that word
	local i, out;					

	if Length(movelist)=1 then return movelist; fi;
	
	out:=StructuralCopy(movelist);
	i:=1;						#i represents position in the word, start at the beginning
	while i<Length(out) do				#while the word has two more entries in positions i, i+1
		if out[i] = invertmove(out[i+1]) then	#if a cancelling pair is detected	
			Remove(out,i);
			Remove(out,i);			#then remove the cancelling pair
			if Length(out)=1 or Length(out)=0 then return out; fi;		#return the word if it is now too short
			if i>1 then i:=i-1; fi;		#back up to catch a new cancelling pair in case we've created one by deleting the last one
			continue;
		else
			i:=i+1;				#increment position in word
		fi;
	od;
	return out;
end;

pw := function(arg)					#takes any number of words as input and returns their freely reduced product (stands for 'product word')
	return freereducemovelist(Concatenation(arg));
end;
cw := function( conjby, conjon)				#takes two words conjby and conjon and returns the freely reduced conjugate conjby * conjon * conjby^{-1}
	return pw(conjby,conjon,iw(conjby));
end;
commw:=function(w1,w2)
	return pw(w1,w2,iw(w1),iw(w2));
end;

genof := function(syl)					#takes a syllable "x^n" in the free group and returns the base "x" of the syllable 
	return ObjByExtRep(FamilyObj(syl),[ExtRepOfObj(syl)[1],1]);
end;
wellformedkgen := function(move)			#returns true if given a list correctly rerpesenting a generator from $S_K$
	if not IsList(move) then return false; 
	elif Length(move)=0 then return false;
	elif move[1]="C" then
		if Length(move)<> 3 then return false;
		elif (move[2]=y) and (move[3]<>y and move[3]<>y^-1) then return true;   # e.g. ["C",y,xa],["C",y,xa^-1]
		elif (move[3]=y or move[3]=y^-1) and move[2]<>y and move[2]<>y^-1 and move[2]=genof(move[2]) then return true;   # e.g. ["C",xa,y],["C",xa,y^-1]
		else return false; fi;
	elif move[1]="Mc" then
		if Length(move)<>4 then return false;
		elif move[2]=y or move[2]=y^-1 then return false;
		elif (move[3]=y or move[3]=y^-1) and move[4]<>y and move[4]<>y^-1 then return true;	#e.g. ["Mc",xa,y,xb]
		elif (move[4]=y or move[4]=y^-1) and move[3]<>y and move[3]<>y^-1 then return true;	#e.g. ["Mc",xa,xb,y]
		else return false; fi;
	else return false;	fi;
end;

ispositive := function(mov)	#returns true if a given $S_Q$ or $S_K$ generator is a positive one
	if mov[1]="M" or mov[1]="C" then		#"M" and "C" generators are positive if their last parameter is
		if ExtRepOfObj(mov[3])[2]<0 then
			return false;
		else 
			return true;
		fi;
	elif mov[1]="Mc" then				#"Mc" generators are positive if their second to last parameter is y or y^-1
		if mov[4] = y or mov[4] = y^-1 then
			return false;
		else
			return true;
		fi;
	else
		return true;				#"P" and "I" generators are always positive
	fi;
end;

applyrels := function(startword, rels)                  #Recursively inserts given relations at given locations in a given word
	if Length(rels)=0 then 
		return startword;
	elif rels[1][1]=0 then
		return applyrels( pw(rels[1][2],startword) , rels{[2..Length(rels)]});
	else
		return applyrels( pw(startword{[1..rels[1][1]]},rels[1][2],startword{[(rels[1][1]+1)..Length(startword)]}) , rels{[2..Length(rels)]});
	fi;
end;

cyw := function(sh,word)			      #cyclically permutes a given word 
	if Length(word)=0 or sh=0 then return word;
	elif sh>0 then
		return pw(word{[sh+1..Length(word)]},word{[1..sh]});
	else
		return pw(word{[Length(word)+sh+1..Length(word)]},word{[1..Length(word)+sh]});
	fi;
end;



# Functions for interpreting $S_A\cup S_K\cup S_Q$ generators as automorphisms and evaluating them


swap := function(aa,bb)	#returns a function that acts on words in fg by swapping the inputs, which must be letters in fg
	local move;
	move := function(xx)
		return MappedWord(xx, [genof(aa),genof(bb)],[genof(bb),genof(aa)]);
	end;
	return move;
end;
inversionmove := function(aa)	#returns a function that acts on words in fg by inverting the input letter, which must be a letter in fg
	local move;
	move := function(xx)
		return EliminatedWord(xx,genof(aa), Inverse(genof(aa)));
	end;
	return move;
end;

mul := function(aa,bb)		# counterpart of ["M",xa,xb], etc as function on fg
	local move, gen, exp;
	gen:= ObjByExtRep(FamilyObj(aa),[ExtRepOfObj(aa)[1],1]);
	exp:=ExtRepOfObj(aa)[2];
	#Print(exp,"\n");
	if exp > 1 then
		exp:=1;
	elif exp < -1 then
		exp:=-1;
	fi;
	move := function(xx)
		if exp=1 then
			return EliminatedWord(xx, gen, bb*gen);
		elif exp=-1 then
			return EliminatedWord(xx, gen, gen*Inverse(bb));
		fi;
	end;
	return move;
end;
con := function(aa,bb)		# counterpart of ["C",xa,y], etc, as function on fg
	local move;
	move := function(xx)
		return mul(aa,bb)(mul(Inverse(aa),bb)(xx));
	end;
	return move;
end;
mulcomm := function(aa,bb,cc)	# counterpart of ["Mc",xa,y,xb], etc as function on fg
	return mul(aa,bb*cc*Inverse(bb)*Inverse(cc));
end;
wordtolistoffunctions:=function(listoflist) 	#takes a word in $S_K\cup S_Q$ generators, returns the corresponding list of functions on fg
	local out, list;
	out:=[];
	for list in listoflist do
		if list[1]="M" then
			Add(out,mul(list[2],list[3]));
		elif list[1]="C" then
			Add(out,con(list[2],list[3]));
		elif list[1]="Mc" then
			Add(out,mulcomm(list[2],list[3],list[4]));
		elif list[1]="P" then
			Add(out,swap(list[2],list[3]));
		elif list[1]="I" then
			Add(out, inversionmove(list[2]));
		fi;
	od;
	return out;
end;
composemoves := function(list)		#takes a list of functions on fg and returns a single function that computes their composition
	local fn;
	fn := function(vv)
		if Length(list) = 1 then
			return list[1](vv);
		elif Length(list) = 0 then
			return vv;
		else
			return list[1](composemoves(list{[2 ..Length(list)]})(vv));
		fi;
	end;
	return fn;
end;
basischeck := function(move)	#takes a function on fg and returns a list consisting of the images of all generators under this function
	return List(GeneratorsOfGroup(fg), move);
end;
checkpairfns := function(pair)	#takes a pair of functions on fg and returns true if the have the same action on generators, false otherwise
	local left, right;
	left := basischeck(composemoves(pair[1]));
	right := basischeck(composemoves(pair[2]));
	if left=right then
		return true;
	else
		return false;
	fi;	
end;
checkpair := function(pair)	#takes a pair of words and returns true if they represent the same automorphism of fg, false otherwise
	return checkpairfns([wordtolistoffunctions(pair[1]),wordtolistoffunctions(pair[2])]);
end;

# functions encoding basic and extra relations for the Birman exact sequence kernel

krel := function(relno, params)	#takes index number relno and parameter list params and returns corresponding relation in $\Gamma$ (as a word).  Returns [] if given bad data
	local m1, m2, m3;
	if relno=1 then		#relation #1: e.g. ["C",xa,y] commutes with ["C",xb,y]
		m1:=["C",genof(params[1]),y]; 
		m2 := ["C",genof(params[2]),y];
		if wellformedkgen(m1) and wellformedkgen(m2) then return [m1,m2,invertmove(m1),invertmove(m2)]; 
		else return []; 
		fi;
	elif relno=2 then	#e.g. ["Mc",xa,y,xb] commutes with ["Mc",xc,y,xd], ["Mc",xa,y,xb] commutes with ["Mc",xa^-1,xc,y],etc.	
		m1:=["Mc",params[1],params[2],params[3]];
		m2:=["Mc",params[4],params[5],params[6]];
		if wellformedkgen(m1) and wellformedkgen(m2) 
			and m1[2]<>m2[3] and m1[2]<>m2[3]^-1 and m1[2]<>m2[4] and m1[2]<>m2[4]^-1 
			and m2[2]<>m1[3] and m2[2]<>m1[3]^-1 and m2[2]<>m1[4] and m2[2]<>m1[4]^-1 and m1[2]<>m2[2]
			then return [m1, m2, invertmove(m1),invertmove(m2)];
		else return [];
		fi;
	elif relno=3 then	#e.g. ["C",xa,y] commutes with ["Mc",xb,y,xc]
		m1:=["C", params[4],y];
		m2:=["Mc",params[1],params[2],params[3]];
		if wellformedkgen(m1) and wellformedkgen(m2)
			and m1[2]<>m2[3] and m1[2]<>m2[3]^-1 and m1[2]<>m2[4] and m1[2]<>m2[4]^-1
			and m1[2]<>m2[2] and m1[2]<>m2[2]^-1
			then return [m1, m2, invertmove(m1),invertmove(m2)];
		else return [];
		fi;
	elif relno=4 then     	#e.g. returns  [ [ "C", y, xb^-1 ], [ "Mc", xa, y, xb ], [ "C", y, xb ], [ "Mc", xa, y, xb^-1 ] ]
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["C",y,params[3]];
		if wellformedkgen(m1) and wellformedkgen(m2) then
			return [invertmove(m1),m2,m1,["Mc",params[1],params[2],params[3]^-1]];
		else return [];
		fi;
	elif relno=5 then 	#e.g. returns [ [ "C", xb, y^-1 ], [ "Mc", xa, y, xb ], [ "C", xb, y ], [ "Mc", xa, y^-1, xb ] ]
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["C",genof(params[3]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [invertmove(m1),m2,m1,["Mc",params[1],params[2]^-1,params[3]]];
		else return [];
		fi;
	elif relno=6 then	#e.g. returns [ [ "C", xa, y ], [ "Mc", xa, y, xb ], [ "C", xa, y^-1 ], [ "Mc", xa, y^-1, xb ] ]
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["C",genof(params[1]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) then
			return [m1,m2,invertmove(m1),["Mc",params[1],params[2]^-1,params[3]]];
		else return [];
		fi;
	elif relno=7 then  	#e.g. returns [ [ "Mc", xa, y, xb ], [ "Mc", xa^-1, y, xb ], [ "C", xa, y^-1 ], [ "C", y, xb ], [ "C", xa, y ], [ "C", y, xb^-1 ] ]
		m1:=["Mc",params[1],params[2],params[3]];
		m2:=["C",y,params[3]];
		m3:=["C",genof(params[1]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) then
			return [m1,["Mc",params[1]^-1,params[2],params[3]],invertmove(m3),m2,m3,invertmove(m2)];
		else return [];
		fi;
	elif relno=8 then	#relation that rewrites, e.g. [ [ "Mc", xb, y^-1, xc ], [ "Mc", xa, y, xb ], [ "Mc", xb, xc, y^-1 ]]
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3],params[2]^-1,params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [m1,m2,invertmove(m1),["Mc",params[1],params[2],params[4]],invertmove(m2),["Mc",params[1],params[2]^-1,params[4]]];
		else return [];
		fi;
	elif relno=9 then	#relation that rewrites, e.g.  [ [ "C", xb, y^-1 ], [ "C", y, xc ], [ "Mc", xa, y, xb ], [ "C", y, xc^-1 ], [ "C", xb, y ]]
		m3:=["Mc",params[1],params[2],params[3]];
		m2:=["C",y,params[4]];
		m1:=["C",genof(params[3]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) and (params[2]=y or params[2]=y^-1) then
			return [invertmove(m1),m2,m3,invertmove(m2),m1,["Mc",params[1],params[2],params[4]],m3,["Mc",params[1],params[4],params[2]],m2,invertmove(m3),invertmove(m2),["Mc",params[1],params[2]^-1,params[3]]];
		else return [];
		fi;
	elif relno=10 then	#relations that rewrites, e.g. [[ "C", xc, y^-1 ], [ "C", y, xc ], [ "Mc", xa, y, xb ], [ "C", y, xc^-1 ],[ "C", xc, y ]]
		m3:=["Mc",params[1],params[2],params[3]];
		m2:=["C",y,params[4]];
		m1:=["C",genof(params[4]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) then
			return [invertmove(m1),m2,m3,invertmove(m2),m1,["Mc",params[1],params[4],params[2]^-1],invertmove(m3),m2,["Mc",params[1],params[2]^-1,params[3]],invertmove(m2),["Mc",params[1],params[2]^-1,params[4]],["Mc",params[1],params[3],params[2]^-1]];
		else return[];
		fi;
	else return [];
	fi;
end;

exkrel := function(relno,params)  #given index number and parameter list, returns auxiliary relations that follow from original relations
	local m1,m2,m3;
	if relno=1 then		#returns, e.g. [ [ "C", xb, y ], [ "Mc", xa, y, xb ], [ "C", xb, y^-1 ], [ "C", xa, y^-1 ],[ "Mc", xa, xb, y ], [ "C", xa, y ] ]
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["C",genof(params[1]),params[2]];
		m3:=["C",genof(params[3]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) then
			return [m3,m2,invertmove(m3),invertmove(m1),invertmove(m2),m1];
		else return [];
		fi;
	elif relno = 2 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3],params[2]^-1,params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [invertmove(m1),m2,m1,["Mc",params[1],params[4],params[2]],invertmove(m2),["Mc",params[1],params[4],params[2]^-1]];
		else return [];
		fi;
	elif relno = 3 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3],params[2],params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [invertmove(m1),m2,m1,["C",genof(params[4]),params[2]],["Mc",params[1],params[2],params[4]],["C",genof(params[4]),params[2]^-1],invertmove(m2),["Mc",params[1],params[4],params[2]]];
		else return [];
		fi;
	elif relno = 4 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3],params[2],params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [m1,m2,invertmove(m1),["C",genof(params[4]),params[2]],["Mc",params[1],params[4],params[2]],["C",genof(params[4]),params[2]^-1],invertmove(m2),["Mc",params[1],params[2],params[4]]];	
		else return [];
		fi;
	elif relno = 5 then	#variation on relation 9
		m3:=["Mc",params[1],params[2],params[3]];
		m2:=["C",y,params[4]];
		m1:=["C",genof(params[3]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) and (params[2]=y or params[2]=y^-1)  then
			return [m1,m2,m3,invertmove(m2),invertmove(m1),["Mc",params[1],params[2],params[4]],["C",genof(params[1]),params[2]^-1],invertmove(m3),["C",genof(params[1]),params[2]],["Mc",params[1],params[4],params[2]],m2,invertmove(m3),invertmove(m2),m3];
		else return [];
		fi;
	elif relno = 6 then	#variation on relation 10, not used, candidate for deletion
		m3:=["Mc",params[1],params[2],params[3]];
		m2:=["C",y,params[4]];
		m1:=["C",genof(params[4]),params[2]];
		if wellformedkgen(m1) and wellformedkgen(m2) and wellformedkgen(m3) and (params[2]=y or params[2]=y^-1) then
			return [m1, m2, m3, invertmove(m2), invertmove(m1), [ "C", genof(params[1]), params[2]^-1], [ "Mc", params[1], params[2], params[4] ], m3, [ "Mc", params[1], params[4], params[2] ], [ "C", y, params[4] ], invertmove(m3), [ "C", y, params[4]^-1 ], [ "Mc", params[1], params[2]^-1, params[3] ], [ "C", genof(params[1]), params[2] ] ];
		else return [];
		fi;
	elif relno = 7 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3]^-1,params[2]^-1,params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [ invertmove(m1), m2, m1, invertmove(m2), [ "C", y, params[4] ], m2, [ "C", y, params[4]^-1 ], [ "Mc", params[1], params[2], params[4] ], invertmove(m2), [ "C", y, params[4]], [ "Mc", params[1], params[2]^-1, params[3]], [ "C", y, params[4]^-1 ], [ "Mc", params[1], params[2]^-1, params[4]], [ "Mc", params[1], params[3], params[2]^-1 ] ];
		fi;
	elif relno = 8 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3]^-1,params[2]^-1,params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [m1, m2, invertmove(m1), [ "Mc", params[1], params[4], params[2] ], [ "C", y, params[4] ], invertmove(m2), [ "C", y, params[4]^-1 ], [ "Mc", params[1], params[2]^-1, params[3] ], [ "Mc", params[1], params[4], params[2]^-1 ], [ "C", y, params[4] ], [ "Mc", params[1], params[3], params[2]^-1 ], [ "C", y, params[4]^-1 ] ];
		else return [];
		fi;
	elif relno=9 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3]^-1,params[2],params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [invertmove(m1),m2,m1,["C",genof(params[1]),params[2]^-1],m2,["Mc",params[1],params[4],params[2]],["C",y,params[4]],invertmove(m2),["C",y,params[4]^-1],["Mc",params[1],params[2]^-1,params[3]],[ "C", genof(params[1]), params[2] ], [ "C", y, params[4] ], m2, [ "C", y, params[4]^-1 ], [ "Mc", params[1], params[2], params[4] ], invertmove(m2)];
		else return [];
		fi;
	elif relno=10 then	#variation on relation 8
		m2:=["Mc",params[1],params[2],params[3]];
		m1:=["Mc",params[3]^-1,params[2],params[4]];
		if wellformedkgen(m1) and wellformedkgen(m2) and (params[2]=y or params[2]=y^-1) then
			return [ m1, m2, invertmove(m1), [ "C", genof(params[1]), params[2]^-1 ], [ "Mc", params[1], params[2], params[4] ], [ "C", y, params[4] ], [ "Mc", params[1], params[2], params[4]^-1 ], m2, [ "Mc", params[1], params[4]^-1, params[2] ], [ "C", y, params[4]^-1 ], invertmove(m2), [ "C", y, params[4] ], [ "Mc", params[1], params[2]^-1, params[3] ], [ "C", y, params[4]^-1 ], [ "C", genof(params[1]), params[2] ], [ "Mc", params[1], params[4], params[2] ] ];
		else return [];
		fi;
	else
		return [];
	fi;
end;

#Functions defining $\phi$, the lifted outer action

phiongens := function(by,on)	#action function $\phi$ in the special case that both inputs are single generators.  Refer to the table defining phi. returns a word.
	if not ispositive(on) then
		return iw(phiongens(by,invertmove(on)));	#define action on nonpositive generators by acting on inverses
	fi;
	if by[1]="M" then
		if by[3]=y or by[3]=y^-1 then
			if on[1]="C" and (on[2]=y or on[2]=y^-1) then
				if by[2]<>on[3] and by[2]<>on[3]^-1 then
					return [on,["Mc",by[2],by[3]^-1,on[3]^-1]];
				else 
					return [["C",genof(by[2]),by[3]],on];
				fi;
			elif on[1]="C" then
				return [on];
			elif on[1]="Mc" then
				if (on[2]=by[2]) or (on[4]=by[2]) then
				return [["C",genof(by[2]),by[3]],on,["C",genof(by[2]),by[3]^-1]];
				else return [on];
				fi;
			fi;
		else
			if on[1]="C" and (on[2]=y or on[2]=y^-1) then
				if on[3] = by[2] then
					return [on,["C",y,by[3]]];
				elif on[3] = by[2]^-1 then
					return [["C",y,by[3]^-1],on];
				else return [on];
				fi;
			elif on[1]="C" then
				if on[2] = by[2] or on[2] = by[2]^-1 then
					return [on,["Mc",by[2],by[3]^-1,y]];
				elif on[2]=by[3] or on[2] = by[3]^-1 then
					return [on,["Mc",by[2],by[3]^-1,y^-1]];
				else return [on];
				fi;
			elif on[1]="Mc" then
				if on[2]=by[2] and on[4]<>by[3] and on[4]<>by[3]^-1 then
					return [["C",y,on[4]],["Mc",on[2],on[3],by[3]^-1],["C",y,on[4]^-1],on,["Mc",on[2],by[3]^-1,on[3]]];
				elif on[2]=by[2] and on[4]=by[3]^-1 then
					return [["C",y,by[3]^-1],on,["C",y,by[3]]];
				elif on[2]=by[2] and on[4]=by[3] then
					return [["Mc",on[2],on[4]^-1,on[3]]];
				elif on[2]=by[3] and on[4]<>by[2] and on[4]<>by[2]^-1 then
					return [on,["Mc",by[2],on[3],by[3]^-1],["Mc",by[2],on[4],on[3]],["C",y,on[4]],["Mc",by[2],by[3]^-1,on[3]],["C",y,on[4]^-1]];
				elif on[2]=by[3]^-1 and on[4]<>by[2] and on[4]<>by[2]^-1 then
					return [on,["Mc",by[2],on[3],on[4]]];
				elif on[4]=by[2] and on[2]<>by[3] and on[2]<>by[3]^-1 then
					return [["C",y,by[2]],["Mc",on[2],on[3],by[3]],["C",y,by[2]^-1],on];
					#return [["C",y,by[2]],["Mc",on[2],on[3],by[3]],["Mc",on[2],on[4]^-1,on[3]],["C",y,by[2]^-1]];
				elif on[4]=by[2]^-1 and on[2]<>by[3] and on[2]<>by[3]^-1 then
					return [["C",y,by[3]^-1],on,["Mc",on[2],by[3],on[3]],["C",y,by[3]]];
				elif on[4]=by[2] and on[2]=by[3] then
					return [["Mc",on[2]^-1,on[3]^-1,on[4]],["C",genof(on[2]),on[3]],["Mc",on[4],on[3],on[2]^-1],["C",genof(on[4]),on[3]^-1]];
				elif on[4]=by[2]^-1 and on[2]=by[3] then
					return [["C",y,on[2]^-1],["C",y,on[4]],["C",genof(on[4]),on[3]],["Mc",on[4]^-1,on[2]^-1,on[3]],["C",genof(on[2]),on[3]^-1],["Mc",on[2]^-1,on[4]^-1,on[3]^-1],["C",y,on[4]^-1],["C",y,on[2]]];
				elif on[4]=by[2] and on[2]=by[3]^-1 then
					return [["C",y,on[4]],["C",y,on[2]^-1],["C",genof(on[2]),on[3]^-1],["Mc",on[4],on[2],on[3]],["C",y,on[2]],["Mc",on[2],on[4]^-1,on[3]],["C",y,on[4]^-1],["C",genof(on[4]),on[3]]];
				elif on[4]=by[2]^-1 and on[2]=by[3]^-1 then
					return [["C",y,on[2]],["C",y,on[4]],["C",genof(on[4]),on[3]^-1],["C",y,on[4]^-1],on,["C",y,on[2]^-1],["Mc",on[4]^-1,on[3],on[2]],["C",genof(on[2]),on[3]]];
				else return [on];
				fi;
			fi;
		fi;
	elif by[1]="P" then
		if on[1]="Mc" then
			return [["Mc",swap(by[2],by[3])(on[2]),swap(by[2],by[3])(on[3]),swap(by[2],by[3])(on[4])]];
		elif on[1]="C" then
			return [["C",swap(by[2],by[3])(on[2]),swap(by[2],by[3])(on[3])]];
		fi;
	elif by[1]="I" then
		if on[1]="Mc" then
			return [["Mc",inversionmove(by[2])(on[2]),inversionmove(by[2])(on[3]),inversionmove(by[2])(on[4])]];
		elif on[1]="C" then
			return [["C",on[2],inversionmove(by[2])(on[3])]];
		fi;
	fi;
end;
phigenword := function(by,list) #phi in special case input is a (generator, word) pair
	local out, on;
	out:=[];
	for on in list do
		Append(out,phiongens(by,on));
	od;
	return freereducemovelist(out);
end;
phi := function(bylist,onlist)	#phi in general case, input is a pair of words
	local bymove, bybackwards, out;
	if bylist=[] then return onlist; fi;
	out:=onlist;
	bybackwards:=Reversed(bylist);
	for bymove in bybackwards do
		out := phigenword(bymove, out);
	od;
	return out;
end;


#  Functions for the action $\psi$. This is a standard action of $\Aut(F_n)$ on $\Z^n$.

psiongens := function(fmove,zmove) 	#action psi in special case both inputs are generators.   
	local a,b;

	if fmove[1]="M" and genof(fmove[3])=zmove[2] then
		if fmove[2]=genof(fmove[2]) then
			a:=1;
		else
			a:=-1;
		fi;
		if fmove[3]=genof(fmove[3]) then
			b:=1;
		else
			b:=-1;
		fi;
		return [zmove,["M",genof(fmove[2]),zmove[3]^(-a*b)]];
	elif fmove[1]="I" and genof(fmove[2])=zmove[2] then
		return [invertmove(zmove)];
	elif fmove[1]="P" then
		return [["M", swap(fmove[2],fmove[3])(zmove[2]), zmove[3]]];
	else
		return [zmove];
	fi;
end;
psigenword := function(by,list)		#action psi in special case first input is a generator, second input is a word
	local out, on;
	out:=[];
	for on in list do
		Append(out,psiongens(by,on));
	od;
	return freereducemovelist(out);
end;
psi := function(bylist,onlist)		#action psi in the general case
	local bymove, bybackwards, out;
	if bylist=[] then return onlist; fi;
	out:=onlist;
	bybackwards:=Reversed(bylist);
	for bymove in bybackwards do
		out := psigenword(bymove, out);
	od;
	return out;
end;



# Functions for the twisted bilinear map $\lambda$, which is essentially the cocycle for the extension of $\Gamma$.

lambdaongens := function(fmove,zmove)  #lambda in the special case that both inputs are generators
	if fmove[1]="P" then
		return [];
	elif fmove[1]="I" then
		if genof(zmove[2])=genof(fmove[2]) then
			return [["C",genof(zmove[2]),zmove[3]]];
		else
			return [];
		fi;
	elif fmove[1]="M" then
		if fmove[2]=zmove[2] then
			return [["Mc",fmove[2],zmove[3]^-1,fmove[3]^-1]];
		elif fmove[3]=zmove[2] then
			if fmove[2]=genof(fmove[2]) then
				return [["Mc",fmove[2],zmove[3],fmove[3]^-1]];
			else
				if ispositive(zmove) then
					return [["Mc",fmove[2],y,fmove[3]^-1],["C",genof(fmove[2]),y^-1]];
				else
					return [["C",genof(fmove[2]),y],["Mc",fmove[2],fmove[3]^-1,y]]; 
				fi;
			fi;
		elif fmove[3]=zmove[2]^-1 then
			if fmove[2]<>genof(fmove[2]) then 
				return [["C",genof(fmove[2]),zmove[3]]];
			else 
				return [];
			fi;
		else
			return [];
		fi;
	fi;
end;
lambdagenword := function(fmove, zlist)  #lambda in the special case that the first input is a generator and the second is a word.
	local newlist;
	if Length(zlist)=0 then return []; fi;
	if Length(zlist)=1 then
		return lambdaongens(fmove,zlist[1]);
	else
		newlist := List(zlist);
		Remove(newlist,1);
		return pw(lambdaongens(fmove,zlist[1]),phi(psi([fmove],[zlist[1]]),lambdagenword(fmove,newlist)));  #uses twisted commutator expansion identity for second input
	fi;
end;
lambda := function(flist,zlist)  #lambda in the general case.  both inputs are words.
	local newlist;
	if Length(flist)=0 then return [];
	elif Length(flist)=1 then
		return lambdagenword(flist[1],zlist);
	else
		newlist := List(flist);
		Remove(newlist,1);
		return pw(phi([flist[1]],lambda(newlist,zlist)),lambdagenword(flist[1],psi(newlist,zlist)));  #uses twisted commutator expansion identity for first input
	fi;
end;






# Verifying extra relations for $\Gamma$ follow from listed relations for $\Gamma$.

exkrellist:=
[
# exkrel(1,[xa,y,xb]),
	applyrels(exkrel(1,[xa,y,xb]),[[4,krel(1,[xa,xb])],[4,krel(5,[xa,y^-1,xb])],[4,iw(krel(6,[xa,y,xb]))],[3,krel(1,[xb,xa])]]),
# exkrel(2,[xa,y,xb,xc]),
	applyrels(exkrel(2,[xa,y,xb,xc]),[[2,krel(2,[xa,xc,y,xb,y^-1,xc])],[3,cyw(3,krel(8,[xa,y,xb,xc]))],[0,krel(2,[xa,y^-1,xc,xb,xc,y^-1])]]),
# exkrel(3,[xa,y,xb,xc]),
	applyrels(exkrel(3,[xa,y,xb,xc]),[[3,iw(krel(5,[xb,y^-1,xc]))],[1,krel(3,[xa,y,xb,xc])],[6,krel(3,[xa,xb,y,xc])],[2,cyw(-1,iw(krel(8,[xa,y,xb,xc])))],[0,krel(5,[xb,y^-1,xc])],[1,krel(5,[xa,y,xc])]]),
# exkrel(4,[xa,y,xb,xc]),
	applyrels(exkrel(4,[xa,y,xb,xc]),[[2,krel(5,[xb,y^-1,xc])],[1,krel(3,[xa,y,xb,xc])],[6,krel(3,[xa,xb,y,xc])],[3,krel(2,[xa,xc,y,xb,y^-1,xc])],[6,cyw(1,krel(8,[xa,y,xb,xc]))],[2,krel(2,[xb,y^-1,xc,xa,y^-1,xc])],[1,iw(krel(5,[xb,y^-1,xc]))],[0,iw(krel(5,[xa,y^-1,xc]))]]),
# exkrel(5,[xa,y,xb,xc]),
	applyrels(exkrel(5,[xa,y,xb,xc]),[[5,krel(3,[xa,y,xc,xb])],[7,krel(1,[xa,xb])],[7,krel(5,[xa,y^-1,xb])],[8,krel(1,[xb,xa])],[9,krel(3,[xa,xc,y,xb])],[9,cyw(5,krel(9,[xa,y,xb,xc]))],[14,iw(krel(5,[xa,y,xb]))],[7,iw(krel(6,[xa,y,xb]))]]),
# exkrel(6,[xa,y^-1,xb,xc]),
	applyrels(exkrel(6,[xa,y^-1,xb,xc]),[[4,krel(1,[xa,xc])],[7,iw(krel(5,[xa,y,xc]))],[6,iw(krel(3,[xa,y^-1,xb,xc]))],[8,krel(5,[xa,y,xc])],[8,cyw(5,krel(10,[xa,y^-1,xb,xc]))],[11,iw(krel(3,[xa,y,xb,xc]))],[11,cyw(2,krel(1,[xc,xa]))],[7,krel(4,[xa,y,xc])],[3,krel(7,[xa^-1,y^-1,xc^-1])],[5,iw(krel(6,[xa,y,xc^-1]))],[2,krel(2,[xa^-1,y^-1,xc^-1,xa,y^-1,xb])],[4,iw(krel(6,[xa,y,xb]))],[4,iw(krel(4,[xa,y,xc]))],[4,krel(6,[xa,y^-1,xc^-1])],[2,iw(krel(7,[xa^-1,y^-1,xc^-1]))]]),
# exkrel(7,[xa,y^-1,xb^-1,xc])
	applyrels(exkrel(7,[xa,y,xb,xc]),[[3,cyw(-2,iw(krel(7,[xb,y^-1,xc])))],[0,cyw(2,krel(7,[xb,y^-1,xc]))],[4,iw(krel(8,[xa,y,xb,xc]))],[4,krel(4,[xa,y^-1,xc^-1])],[8,krel(4,[xa,y,xc])],[3,krel(3,[xa,y^-1,xc^-1,xb])],[7,krel(3,[xa,y,xc^-1,xb])],[3,iw(krel(9,[xa,y,xb,xc^-1]))],[1,iw(krel(4,[xa,y^-1,xc^-1]))],[0,iw(krel(3,[xa,xc,y^-1,xb]))],[1,cyw(5,krel(9,[xa,y^-1,xb,xc]))],[6,iw(exkrel(1,[xa,y,xb]))],[12,iw(krel(4,[xa,y,xc]))],[9,iw(krel(3,[xa,xc,y,xb]))],[15,exkrel(5,[xa,y,xb,xc])]]),
# exkrel(8,[xa,y,xb,xc]),
	applyrels(exkrel(8,[xa,y,xb,xc]),[[3,krel(7,[xb^-1,y^-1,xc])],[0,iw(krel(7,[xb^-1,y^-1,xc]))],[4,iw(exkrel(2,[xa,y,xb,xc]))],[4,krel(3,[xa,y^-1,xc,xb])],[7,iw(krel(3,[xa,xc,y,xb]))],[4,iw(krel(5,[xa,y,xb]))],[6,iw(krel(4,[xa,y,xc^-1]))],[4,iw(krel(4,[xa,y^-1,xc^-1]))],[1,iw(krel(3,[xa,xc^-1,y^-1,xb]))],[8,krel(3,[xa,y,xc^-1,xb])],[7,krel(9,[xa,y^-1,xb,xc^-1])],[4,krel(4,[xa,y^-1,xc^-1])],[9,krel(4,[xa,y,xc^-1])]]),
# exkrel(9,[xa,y,xb,xc]),
	applyrels(exkrel(9,[xa,y,xb,xc]),[[3,iw(cyw(2,krel(7,[xb,y,xc])))],[0,cyw(2,krel(7,[xb,y,xc]))],[4,iw(exkrel(4,[xa,y,xb,xc]))],[6,iw(exkrel(1,[xa,y,xc]))],[9,phi([["M",xa,y^-1]],iw(krel(4,[xa,y,xc^-1])))],[4,krel(4,[xa,y,xc^-1])],[2,iw(krel(3,[xa,y,xc^-1,xb]))],[13,krel(3,[xa,y,xc^-1,xb])],[12,phi([["M",xa,y^-1]],krel(3,[xa,y,xc^-1,xb]))],[9,krel(3,[xa,xc^-1,y,xb])],[3,iw(exkrel(5,[xa,y,xb,xc^-1]))],[15,cyw(2,krel(1,[xb,xa]))],[15,iw(exkrel(1,[xa,y,xb]))],[18,iw(krel(3,[xa,xc,y,xb]))],[19,cyw(5,exkrel(5,[xa,y,xb,xc]))],[22,iw(krel(5,[xa,y,xb]))],[19,krel(1,[xa,xb])],[20,iw(exkrel(5,[xa,y,xb,xc]))],[29,iw(krel(3,[xa,y,xc,xb]))],[28,cyw(3,exkrel(1,[xa,y,xb]))],[23,iw(krel(4,[xa,y,xc]))],[7,iw(krel(7,[xa,y,xc^-1]))],[11,krel(6,[xa^-1,y,xc^-1])],[8,krel(2,[xa,y,xb,xa^-1,y^-1,xc^-1])],[9,krel(2,[xa,xc^-1,y,xa^-1,y^-1,xc^-1])],[11,iw(krel(6,[xa^-1,y,xc^-1]))],[13,krel(7,[xa,y,xc^-1])],[11,krel(4,[xa,y,xc^-1])]]),
# exkrel(10,[xa,y,xb,xc]),
	applyrels(exkrel(10,[xa,y,xb,xc]),[[2,iw(krel(6,[xa,y^-1,xb]))],[2,krel(3,[xb^-1,xc,y,xa])],[3,iw(krel(3,[xb^-1,xc,y,xa]))],[4,exkrel(8,[xa,y^-1,xb,xc])],[1,krel(6,[xa,y,xc])],[8,krel(4,[xa,y,xc])],[9,iw(krel(4,[xa,y,xc]))]]),
];

# Verifying that $\phi$ acts by conjugation

phiconjugationcheck:=function(bygen,ongen)
	return checkpair([phi([bygen],[ongen]),cw([bygen],[ongen])]);
end;

phiconjugationlist:=
[
phiconjugationcheck(["M",xa,y],["C",xb,y]),
phiconjugationcheck(["M",xa,y],["C",xa,y]),
phiconjugationcheck(["M",xa,y],["C",y,xb]),
phiconjugationcheck(["M",xa,y],["C",y,xa]),
phiconjugationcheck(["M",xa,y],["Mc",xb,y,xc]),
phiconjugationcheck(["M",xa,y],["Mc",xb,y^-1,xc]),
phiconjugationcheck(["M",xa,y],["Mc",xa,y,xb]),
phiconjugationcheck(["M",xa,y],["Mc",xa^-1,y,xb]),
phiconjugationcheck(["M",xa,y],["Mc",xa,y^-1,xb]),
phiconjugationcheck(["M",xa,y],["Mc",xa^-1,y^-1,xb]),
phiconjugationcheck(["M",xa,y],["Mc",xb,y,xa]),
phiconjugationcheck(["M",xa,y],["Mc",xb^-1,y,xa]),
phiconjugationcheck(["M",xa,y],["Mc",xb,y^-1,xa]),
phiconjugationcheck(["M",xa,y],["Mc",xb^-1,y^-1,xa]),

phiconjugationcheck(["M",xa,xb],["C",xc,y]),
phiconjugationcheck(["M",xa,xb],["C",xa,y]),
phiconjugationcheck(["M",xa,xb],["C",xb,y]),
phiconjugationcheck(["M",xa,xb],["C",y,xc]),
phiconjugationcheck(["M",xa,xb],["C",y,xa]),
phiconjugationcheck(["M",xa,xb],["C",y,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y,xd]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y^-1,xd]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y^-1,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y^-1,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y^-1,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y,xa^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y^-1,xa^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y^-1,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y^-1,xc]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y^-1,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xc,y^-1,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y^-1,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y^-1,xb]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xa,y^-1,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xa^-1,y^-1,xb^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y^-1,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y^-1,xa]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y,xa^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y,xa^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xb,y^-1,xa^-1]),
phiconjugationcheck(["M",xa,xb],["Mc",xb^-1,y^-1,xa^-1]),
];



# Verifying back and forth action of $\phi$ on $\Gamma$ is trivial 

phiinversecheck:=function(by,on)
	return pw(phi(iw([by]),phi([by],[on])),iw([on]));
end;

phiAinverselist:=
[
phiinversecheck(["M",xa,xb],["C",y,xc]),
phiinversecheck(["M",xa,xb],["C",y,xa]),
phiinversecheck(["M",xa,xb],["C",y,xb]),
phiinversecheck(["M",xa,xb],["C",xc,y]),
phiinversecheck(["M",xa,xb],["C",xa,y]),
phiinversecheck(["M",xa,xb],["C",xb,y]),
phiinversecheck(["M",xa,xb],["Mc",xc,y,xd]),
phiinversecheck(["M",xa,xb],["Mc",xa,y,xd]),
#phiinversecheck(["M",xa,xb],["Mc",xc,y,xa]),
	applyrels(phiinversecheck(["M",xa,xb],["Mc",xc,y,xa]),[[1,iw(krel(4,[xc,y,xb]))]]),
phiinversecheck(["M",xa,xb],["Mc",xb,y,xd]),
phiinversecheck(["M",xa,xb],["Mc",xc,y,xb]),
phiinversecheck(["M",xa,xb],["Mc",xa,y,xb]),
#phiinversecheck(["M",xa,xb],["Mc",xb,y,xa]),
	applyrels(phiinversecheck(["M",xa,xb],["Mc",xb,y,xa]),[[3,krel(1,[xb,xa])],[1,iw(exkrel(1,[xa,y^-1,xb]))]])
];

phiZinverselist:=
[
#phiinversecheck(["M",xa,y],["C",y,xb]),
	applyrels(phiinversecheck(["M",xa,y],["C",y,xb]),[[4,iw(krel(6,[xa,y,xb^-1]))]]),
phiinversecheck(["M",xa,y],["C",y,xa]),
phiinversecheck(["M",xa,y],["C",xb,y]),
phiinversecheck(["M",xa,y],["C",xa,y]),
phiinversecheck(["M",xa,y],["Mc",xb,y,xc]),
phiinversecheck(["M",xa,y],["Mc",xa,y,xc]),
phiinversecheck(["M",xa,y],["Mc",xb,y,xa])
];
# Verifying that the action of Nielsen's relations on $\Gamma$ by $\phi$ is trivial

phiN3check:=function(la,lb,on)
	return pw(phi([["M",lb,la],["M",la,lb^-1]],[on]),iw(phi([["M",la^-1,lb^-1],["I",lb],["P",la,lb]],[on])));
end;

phiN3list:=
[
phiN3check(xa,xb,["C",y,xc]), 
phiN3check(xa,xb,["C",y,xa]), 
phiN3check(xa,xb,["C",y,xb]), 
phiN3check(xa,xb,["C",xc,y]), 
#phiN3check(xa,xb,["C",xa,y]),
	applyrels(phiN3check(xa,xb,["C",xa,y]),[[1,krel(6,[xb,y,xa^-1])],[0,krel(1,[xb,xa])]]),
#phiN3check(xa,xb,["C",xb,y]),
	applyrels(phiN3check(xa,xb,["C",xb,y]),[[3,krel(6,[xb,y,xa^-1])]]),
phiN3check(xa,xb,["Mc",xc,y,xd]), 
#phiN3check(xa,xb,["Mc",xa,y,xd]),
	applyrels(phiN3check(xa,xb,["Mc",xa^-1,y,xd]),[[0,krel(2,[xb,y,xd,xa^-1,y,xd])]]),
phiN3check(xa,xb,["Mc",xc,y,xa]), 
#phiN3check(xa,xb,["Mc",xb,y,xd]),
	applyrels(phiN3check(xa,xb,["Mc",xb,y,xd]),[[5,iw(exkrel(10,[xb,y,xa^-1,xd]))],[18,krel(2,[xb,xd,y,xa,y,xd])],[23,krel(4,[xa,y,xd^-1])],[20,iw(krel(4,[xa,y,xd^-1]))],[23,exkrel(9,[xb,y,xa^-1,xd^-1])],[32,iw(krel(4,[xb,y,xd]))],[5,iw(krel(7,[xb,y,xd]))],[11,krel(6,[xb^-1,y,xd])],[7,iw(krel(4,[xb^-1,y^-1,xd]))],[7,krel(2,[xb,xa^-1,y^-1,xb^-1,xd^-1,y^-1])],[10,krel(4,[xb^-1,y^-1,xd^-1])],[9,krel(2,[xb,y,xa^-1,xb^-1,y^-1,xd])],[11,iw(krel(4,[xb^-1,y^-1,xd^-1]))],[11,krel(2,[xb,y,xd^-1,xb^-1,xd^-1,y^-1])],[12,krel(2,[xb,xa^-1,y,xb^-1,xd^-1,y^-1])],[13,krel(2,[xb,xd^-1,y,xb^-1,xd^-1,y^-1])],[16,krel(4,[xb^-1,y^-1,xd^-1])],[15,krel(2,[xb,xd,y,xb^-1,y^-1,xd])],[17,iw(krel(6,[xb^-1,y,xd]))],[19,krel(7,[xb,y,xd])],[17,krel(4,[xb,y,xd])]]),
#phiN3check(xa,xb,["Mc",xc,y,xb]),
	applyrels(phiN3check(xa,xb,["Mc",xc,y,xb]),[[2,iw(krel(4,[xc,y,xb]))]]),
#phiN3check(xa,xb,["Mc",xa,y,xb]),
	applyrels(phiN3check(xa,xb,["Mc",xa,y,xb]),[[3,iw(krel(6,[xa^-1,y,xb]))],[7,iw(krel(6,[xb,y,xa^-1]))]]),
#phiN3check(xa,xb,["Mc",xb,y,xa]),
	applyrels(phiN3check(xa,xb,["Mc",xb,y,xa]),[[6,krel(5,[xb,y,xa^-1])],[4,krel(4,[xa^-1,y^-1,xb])],[4,iw(krel(6,[xa^-1,y,xb^-1]))],[0,krel(7,[xa,y,xb^-1])]]),
];


phiN4check:= function(xxa,xxb,xxc,xxd,on)
	return pw(phi([["M",xxa,xxb],["M",xxc,xxd]],[on]),phi([["M",xxc,xxd],["M",xxa,xxb]],iw([on])));
end;

phiN4list:=
[
phiN4check(xa,xb,xc,xd,["C",y,xe]), 
phiN4check(xa,xb,xc,xd,["C",y,xa]), 
phiN4check(xa,xb,xc,xd,["C",y,xb]),
phiN4check(xa,xb,xc,xd,["C",xe,y]),
phiN4check(xa,xb,xc,xd,["C",xa,y]),
phiN4check(xa,xb,xc,xd,["C",xb,y]),
phiN4check(xa,xb,xc,xd,["Mc",xe,y,xf]),
phiN4check(xa,xb,xc,xd,["Mc",xa,y,xf]),
phiN4check(xa,xb,xc,xd,["Mc",xe,y,xa]),
phiN4check(xa,xb,xc,xd,["Mc",xb,y,xf]),
phiN4check(xa,xb,xc,xd,["Mc",xe,y,xb]),
phiN4check(xa,xb,xc,xd,["Mc",xa,y,xb]),
phiN4check(xa,xb,xc,xd,["Mc",xb,y,xa]),
phiN4check(xa,xb,xc,xd,["Mc",xa,y,xc]),
phiN4check(xa,xb,xc,xd,["Mc",xa,y,xd]),
#phiN4check(xa,xb,xc,xd,["Mc",xd,y,xa]),
	applyrels(phiN4check(xa,xb,xc,xd,["Mc",xd^-1,y,xa^-1]),[[4,krel(2,[xd^-1,y,xb,xc,xb,y])],[2,krel(2,[xc,y,xa^-1,xd^-1,xb,y])]]),
phiN4check(xa,xb,xc,xd,["Mc",xb,y,xd]),

phiN4check(xa,xb,xc,xb,["C",y,xe]), 
phiN4check(xa,xb,xc,xb,["C",y,xa]),
phiN4check(xa,xb,xc,xb,["C",y,xb]),
phiN4check(xa,xb,xc,xb,["C",xe,y]),
phiN4check(xa,xb,xc,xb,["C",xa,y]),
#phiN4check(xa,xb,xc,xb,["C",xb,y]),
	applyrels(phiN4check(xa,xb,xc,xb,["C",xb,y]),[[1,krel(2,[xc,xb^-1,y^-1,xa,xb^-1,y^-1])]]),
phiN4check(xa,xb,xc,xb,["Mc",xe,y,xf]),
phiN4check(xa,xb,xc,xb,["Mc",xa,y,xf]),
phiN4check(xa,xb,xc,xb,["Mc",xe,y,xa]),
#phiN4check(xa,xb,xc,xb,["Mc",xb,y,xf]),
	applyrels(phiN4check(xa,xb,xc,xb,["Mc",xb^-1,y,xf]),[[1,krel(2,[xc,y,xf,xa,y,xf])]]),
phiN4check(xa,xb,xc,xb,["Mc",xe,y,xb]), 
phiN4check(xa,xb,xc,xb,["Mc",xa,y,xb]), 
#phiN4check(xa,xb,xc,xb,["Mc",xb,y,xa]),
	applyrels(phiN4check(xa,xb,xc,xb,["Mc",xb,y,xa]),[[16,krel(3,[xc,xa,y^-1,xb])],[13,krel(2,[xc,y^-1,xb^-1,xa,xb^-1,y])],[16,cyw(1,exkrel(2,[xc,y^-1,xa,xb^-1]))],[13,krel(5,[xc,y,xa])],[13,iw(krel(3,[xc,xb^-1,y,xa]))],[9,krel(4,[xc,y,xb])]]),
#phiN4check(xa,xb,xc,xb,["Mc",xa,y,xc]),
	applyrels(phiN4check(xa,xb,xc,xb,["Mc",xa,y,xc]),[[3,krel(4,[xa,y,xb])]]),

phiN4check(xa,xb,xc,xb^-1,["C",y,xe]), 
phiN4check(xa,xb,xc,xb^-1,["C",y,xa]), 
phiN4check(xa,xb,xc,xb^-1,["C",y,xb]), 
phiN4check(xa,xb,xc,xb^-1,["C",xe,y]), 
phiN4check(xa,xb,xc,xb^-1,["C",xa,y]), 
#phiN4check(xa,xb,xc,xb^-1,["C",xb,y]),
	applyrels(phiN4check(xa,xb,xc,xb^-1,["C",xb,y]),[[1,krel(2,[xc,xb,y^-1,xa,xb^-1,y^-1])]]),
phiN4check(xa,xb,xc,xb^-1,["Mc",xe,y,xf]), 
phiN4check(xa,xb,xc,xb^-1,["Mc",xa,y,xf]),  
phiN4check(xa,xb,xc,xb^-1,["Mc",xe,y,xa]), 
#phiN4check(xa,xb,xc,xb^-1,["Mc",xb,y,xf]),
	applyrels(phiN4check(xa,xb,xc,xb^-1,["Mc",xb,y,xf]),[[11,krel(2,[xc,xf,y,xa,xb^-1,y])],[10,krel(2,[xc,xf,y,xa,y,xf])],[10,krel(4,[xc,y,xf^-1])],[8,krel(2,[xc,y,xf^-1,xa,y,xb^-1])],[5,iw(krel(4,[xc,y,xf]))]]),
phiN4check(xa,xb,xc,xb^-1,["Mc",xe,y,xb]), 
phiN4check(xa,xb,xc,xb^-1,["Mc",xa,y,xb]), 
#phiN4check(xa,xb,xc,xb^-1,["Mc",xb,y,xa]),
	applyrels(phiN4check(xa,xb,xc,xb^-1,["Mc",xb,y,xa]),[[0,phi([["M",xa,xb]],krel(2,[xc,y,xa,xb,y,xa]))],[5,iw(krel(5,[xc,y^-1,xb]))],[4,cyw(3,exkrel(8,[xc,y,xb,xa]))],[4,iw(krel(4,[xb^-1,y^-1,xa]))],[4,iw(exkrel(9,[xc,y^-1,xb,xa^-1]))],[17,krel(4,[xb^-1,y^-1,xa^-1])],[16,krel(2,[xc,y^-1,xa,xb^-1,y^-1,xa])],[20,exkrel(10,[xc,y^-1,xb,xa])],[3,krel(4,[xc,y^-1,xa])],[11,iw(krel(6,[xc,y,xa]))],[12,cyw(1,krel(7,[xc^-1,y,xa]))],[13,iw(krel(4,[xc,y^-1,xa]))],[10,iw(krel(4,[xc^-1,y,xa^-1]))],[9,krel(2,[xc^-1,y,xa^-1,xc,y^-1,xb])],[6,krel(2,[xc^-1,xa^-1,y,xc,y^-1,xa^-1])],[8,krel(4,[xc^-1,y,xa^-1])],[4,krel(2,[xc^-1,y,xa,xc,y^-1,xb])],[3,iw(krel(4,[xc^-1,y,xa]))],[2,krel(2,[xc^-1,xa^-1,y,xc,xb,y])],[2,krel(4,[xc^-1,y,xa])],[4,iw(krel(6,[xc^-1,y^-1,xa]))],[0,krel(7,[xc,y^-1,xa])]]),
phiN4check(xa,xb,xc,xb^-1,["Mc",xa,y,xc]), 

phiN4check(xa,xb,xa^-1,xd,["C",y,xe]), 
phiN4check(xa,xb,xa^-1,xd,["C",y,xa]), 
phiN4check(xa,xb,xa^-1,xd,["C",y,xb]),  
phiN4check(xa,xb,xa^-1,xd,["C",xe,y]), 
#phiN4check(xa,xb,xa^-1,xd,["C",xa,y]),
	applyrels(phiN4check(xa,xb,xa^-1,xd,["C",xa,y]),[[1,krel(2,[xa^-1,xd^-1,y,xa,xb^-1,y])]]),
phiN4check(xa,xb,xa^-1,xd,["C",xb,y]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xe,y,xf]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xa,y,xf]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xe,y,xa]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xb,y,xf]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xe,y,xb]), 
phiN4check(xa,xb,xa^-1,xd,["Mc",xa,y,xb]), 
#phiN4check(xa,xb,xa^-1,xd,["Mc",xb,y,xa]),
	applyrels(phiN4check(xa,xb,xa^-1,xd,["Mc",xb,y,xa]),[[12,krel(4,[xb,y,xd])],[12,iw(krel(3,[xb,xd^-1,y,xa]))],[12,krel(2,[xa^-1,xd^-1,y,xb,y,xd^-1])],[13,cyw(3,exkrel(10,[xa,y,xb^-1,xd^-1]))],[27,iw(krel(6,[xb,y^-1,xd^-1]))],[29,krel(4,[xb,y^-1,xd^-1])],[28,iw(krel(7,[xb,y^-1,xd]))],[14,krel(6,[xa^-1,y,xd^-1])],[13,iw(krel(4,[xa,y,xd]))],[12,iw(krel(4,[xa^-1,y^-1,xd]))],[9,krel(2,[xa^-1,xd,y^-1,xa,xb^-1,y])],[8,krel(2,[xa^-1,xd,y^-1,xa,y,xd])],[8,krel(4,[xa^-1,y^-1,xd^-1])],[6,krel(2,[xa^-1,y^-1,xd^-1,xa,y,xb^-1])],[5,iw(krel(4,[xa^-1,y^-1,xd^-1]))],[5,krel(2,[xa,y^-1,xb^-1,xa^-1,xd,y^-1])],[4,iw(krel(6,[xa,y^-1,xb^-1]))],[7,krel(6,[xa,y^-1,xd^-1])],[5,iw(krel(4,[xa,y^-1,xd^-1]))],[6,krel(7,[xa,y^-1,xd])]]),
phiN4check(xa,xb,xa^-1,xd,["Mc",xa,y,xd]), 
#phiN4check(xa,xb,xa^-1,xd,["Mc",xd,y,xa]),
	applyrels(phiN4check(xa,xb,xa^-1,xd,["Mc",xd^-1,y,xa]),[[8,krel(2,[xd^-1,xb,y,xa^-1,xb,y])],[7,iw(krel(3,[xd^-1,xb,y,xa]))],[2,iw(krel(4,[xa,y,xb^-1]))],[3,krel(7,[xa,y,xb])]]),
phiN4check(xa,xb,xa^-1,xd,["Mc",xb,y,xd]), 

phiN4check(xa,xb,xa^-1,xb,["C",y,xe]), 
phiN4check(xa,xb,xa^-1,xb,["C",y,xa]), 
phiN4check(xa,xb,xa^-1,xb,["C",y,xb]), 
phiN4check(xa,xb,xa^-1,xb,["C",xe,y]), 
#phiN4check(xa,xb,xa^-1,xb,["C",xa,y]),
	applyrels(phiN4check(xa,xb,xa^-1,xb,["C",xa,y]),[[1,krel(2,[xa^-1,xb^-1,y,xa,xb^-1,y])]]),
#phiN4check(xa,xb,xa^-1,xb,["C",xb,y]),
	applyrels(phiN4check(xa,xb,xa^-1,xb,["C",xb,y]),[[1,krel(2,[xa^-1,xb^-1,y^-1,xa,xb^-1,y^-1])]]),
phiN4check(xa,xb,xa^-1,xb,["Mc",xe,y,xf]),
phiN4check(xa,xb,xa^-1,xb,["Mc",xa,y,xf]), 
phiN4check(xa,xb,xa^-1,xb,["Mc",xe,y,xa]), 
#phiN4check(xa,xb,xa^-1,xb,["Mc",xb,y,xf]),
	applyrels(phiN4check(xa,xb,xa^-1,xb,["Mc",xb^-1,y,xf]),[[1,krel(2,[xa^-1,y,xf,xa,y,xf])]]),
phiN4check(xa,xb,xa^-1,xb,["Mc",xe,y,xb]), 
phiN4check(xa,xb,xa^-1,xb,["Mc",xa,y,xb]), 
#phiN4check(xa,xb,xa^-1,xb,["Mc",xb,y,xa]),
	applyrels(phiN4check(xa,xb,xa^-1,xb,["Mc",xb,y,xa]),[[6,krel(7,[xa^-1,y,xb^-1])],[10,krel(7,[xa,y,xb^-1])],[5,krel(4,[xb^-1,y^-1,xa^-1])]]),

phiN4check(xa,xb,xa^-1,xb^-1,["C",y,xe]), 
phiN4check(xa,xb,xa^-1,xb^-1,["C",y,xa]), 
phiN4check(xa,xb,xa^-1,xb^-1,["C",y,xb]), 
phiN4check(xa,xb,xa^-1,xb^-1,["C",xe,y]), 
#phiN4check(xa,xb,xa^-1,xb^-1,["C",xa,y]),
	applyrels(phiN4check(xa,xb,xa^-1,xb^-1,["C",xa,y]),[[1,krel(2,[xa^-1,xb,y,xa,xb^-1,y])]]),
#phiN4check(xa,xb,xa^-1,xb^-1,["C",xb,y]),
	applyrels(phiN4check(xa,xb,xa^-1,xb^-1,["C",xb,y]),[[1,krel(2,[xa^-1,xb,y^-1,xa,xb^-1,y^-1])]]),
phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,y,xf]), 
phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xa,y,xf]), 
phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,y,xa]), 
#phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,y,xf]), 
	applyrels(phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,y,xf]),[[11,krel(2,[xa^-1,xf,y,xa,xb^-1,y])],[10,krel(2,[xa^-1,xf,y,xa,y,xf])],[10,krel(4,[xa^-1,y,xf^-1])],[8,krel(2,[xa^-1,y,xf^-1,xa,y,xb^-1])],[5,iw(krel(4,[xa^-1,y,xf]))]]),
phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,y,xb]), 
phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xa,y,xb]), 
#phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,y,xa]),
	applyrels(phiN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,y,xa]),[[14,krel(5,[xa,y,xb^-1])],[12,krel(2,[xa,y,xb^-1,xa^-1,y,xb])],[14,iw(krel(5,[xa^-1,y^-1,xb]))],[16,krel(6,[xa^-1,y^-1,xb])],[13,krel(1,[xa,xb])],[15,cyw(2,exkrel(1,[xa,y,xb^-1]))],[15,iw(krel(5,[xa^-1,y,xb]))],[15,krel(4,[xa^-1,y,xb])],[14,iw(krel(7,[xa^-1,y,xb^-1]))],[11,iw(krel(4,[xb,y,xa]))],[9,krel(6,[xb,y^-1,xa])],[7,iw(krel(7,[xb^-1,y^-1,xa]))],[4,iw(krel(6,[xa,y^-1,xb^-1]))],[6,krel(4,[xa,y^-1,xb^-1])],[5,iw(krel(7,[xa,y^-1,xb]))]])
];

phiN5check:=function(xxa,xxb,xxc,on)
	return pw(phi([["M",xxb,xxa],["M",xxc,xxb]],[on]),phi([["M",xxc,xxb],["M",xxb,xxa],["M",xxc,xxa]],iw([on])));
end;

phiN5list:=
[
phiN5check(xa,xb,xc,["C",y,xd]), 
phiN5check(xa,xb,xc,["C",y,xa]), 
phiN5check(xa,xb,xc,["C",y,xb]), 
phiN5check(xa,xb,xc,["C",y,xc]), 
phiN5check(xa,xb,xc,["C",xd,y]), 
#phiN5check(xa,xb,xc,["C",xa,y]),
	applyrels(phiN5check(xa,xb,xc,["C",xa,y]),[[3,krel(4,[xb,y^-1,xa^-1])],[2,iw(exkrel(10,[xc,y^-1,xb^-1,xa]))],[16,iw(krel(4,[xb,y^-1,xa^-1]))],[16,krel(2,[xc,y^-1,xa^-1,xb,xa^-1,y^-1])],[20,exkrel(9,[xc,y^-1,xb^-1,xa^-1])],[16,iw(krel(7,[xc,y^-1,xa^-1]))],[18,krel(6,[xc^-1,y^-1,xa^-1])],[15,krel(4,[xc,y^-1,xa])],[10,krel(2,[xc^-1,y,xa^-1,xc,xb^-1,y^-1])],[9,krel(2,[xc^-1,y,xa^-1,xc,y^-1,xa^-1])],[10,iw(krel(4,[xc^-1,y,xa]))],[7,krel(2,[xc^-1,xa,y,xc,y^-1,xb^-1])],[9,krel(4,[xc^-1,y,xa])],[5,krel(2,[xc^-1,y,xa^-1,xc,xb^-1,y])],[3,iw(krel(6,[xc,y,xa]))],[5,krel(4,[xc,y,xa])],[4,iw(krel(7,[xc,y,xa^-1]))]]),
#phiN5check(xa,xb,xc,["C",xb,y]),
	applyrels(phiN5check(xa,xb,xc,["C",xb,y]),[[3,krel(4,[xb,y,xa^-1])],[2,krel(2,[xc,y^-1,xa,xb,y,xa])],[3,cyw(3,exkrel(8,[xc,y^-1,xb^-1,xa]))],[11,iw(krel(4,[xb,y,xa]))],[6,krel(4,[xc,y,xa])]]),
#phiN5check(xa,xb,xc,["C",xc,y]),
	applyrels(phiN5check(xa,xb,xc,["C",xc,y]),[[1,iw(krel(4,[xc,y,xa]))]]),
phiN5check(xa,xb,xc,["Mc",xd,y,xe]), 
#phiN5check(xa,xb,xc,["Mc",xa,y,xe]),
	phiN5check(xa,xb,xc,["Mc",xa^-1,y,xe]),
phiN5check(xa,xb,xc,["Mc",xd,y,xa]), 
#phiN5check(xa,xb,xc,["Mc",xb,y,xe]),
	phiN5check(xa,xb,xc,["Mc",xb^-1,y,xe]),
phiN5check(xa,xb,xc,["Mc",xd,y,xb]), 
#phiN5check(xa,xb,xc,["Mc",xc,y,xe]),
	phiN5check(xa,xb,xc,["Mc",xc^-1,y,xe]),
phiN5check(xa,xb,xc,["Mc",xd,y,xc]), 
#phiN5check(xa,xb,xc,["Mc",xa,y,xb]),
	applyrels(phiN5check(xa,xb,xc,["Mc",xa,y,xb]),[[17,krel(5,[xc,y,xb^-1])],[17,iw(exkrel(5,[xc,y,xb^-1,xa^-1]))],[16,iw(krel(3,[xc,y,xa^-1,xb]))],[16,cyw(2,exkrel(1,[xc,y,xb^-1]))],[6,iw(krel(4,[xc,y,xa^-1]))]]),
#phiN5check(xa,xb,xc,["Mc",xb,y,xa]),
	applyrels(phiN5check(xa,xb,xc,["Mc",xb,y,xa]),[[2,krel(4,[xb,y,xa^-1])],[1,iw(exkrel(10,[xc,y,xb^-1,xa]))],[14,krel(2,[xc,xa,y,xb,y,xa])],[16,iw(krel(4,[xb,y,xa^-1]))],[19,exkrel(9,[xc,y,xb^-1,xa^-1])],[10,krel(4,[xc,y,xa])],[13,krel(7,[xc,y,xa])],[11,iw(krel(6,[xc^-1,y,xa]))],[11,krel(4,[xc^-1,y^-1,xa^-1])],[9,krel(2,[xc^-1,y^-1,xa^-1,xc,xb^-1,y])],[8,krel(2,[xc^-1,y^-1,xa^-1,xc,y,xa^-1])],[7,iw(krel(4,[xc^-1,y^-1,xa^-1]))],[6,krel(2,[xc^-1,xa,y^-1,xc,y,xb^-1])],[8,krel(4,[xc^-1,y^-1,xa])],[4,krel(2,[xc^-1,y^-1,xa^-1,xc,xb^-1,y^-1])],[2,iw(krel(6,[xc,y^-1,xa]))],[4,krel(4,[xc,y^-1,xa])],[3,iw(krel(7,[xc,y^-1,xa^-1]))]]),
#phiN5check(xa,xb,xc,["Mc",xa,y,xc]),
	applyrels(phiN5check(xa,xb,xc,["Mc",xa,y,xc]),[[25,krel(1,[xc,xa])],[25,krel(3,[xc,xb^-1,y^-1,xa])],[26,krel(1,[xa,xb])],[27,krel(3,[xb^-1,xc,y,xa])],[5,iw(krel(4,[xa,y,xc]))],[5,krel(3,[xa,xc^-1,y,xb])],[5,cyw(-3,iw(exkrel(10,[xb,y,xa^-1,xc^-1])))],[17,krel(4,[xb,y,xc^-1])],[4,cyw(-1,iw(krel(7,[xb^-1,y,xc^-1])))],[6,krel(4,[xb^-1,y,xc^-1])],[5,krel(4,[xa,y,xc^-1])],[5,cyw(-1,iw(krel(7,[xa,y,xc])))],[4,krel(6,[xa^-1,y^-1,xc])],[7,krel(3,[xb,xa^-1,y^-1,xc])],[20,krel(6,[xc,y,xb^-1])],[8,krel(2,[xc,xa^-1,y,xb,xa^-1,y^-1])],[11,krel(4,[xb,y^-1,xa^-1])],[12,iw(krel(4,[xb,y^-1,xa^-1]))],[13,exkrel(8,[xc,y,xb^-1,xa])],[12,krel(4,[xc,y,xa])],[13,krel(4,[xc,y^-1,xa])]]),
#phiN5check(xa,xb,xc,["Mc",xc,y,xa]),
	phiN5check(xa,xb,xc,["Mc",xc^-1,y,xa]),
#phiN5check(xa,xb,xc,["Mc",xb,y,xc]),
	applyrels(phiN5check(xa,xb,xc,["Mc",xb^-1,y,xc]),[[6,krel(3,[xc,y,xa,xb])],[4,iw(krel(4,[xb,y,xa]))],[3,krel(7,[xb,y,xa])]]),
#phiN5check(xa,xb,xc,["Mc",xc,y,xb]),
	phiN5check(xa,xb,xc,["Mc",xc^-1,y,xb])
];

# Verifying commutativity in the action of $\Z^n$ on $\Gamma$ by $\phi$.

phizncheck:= function(xxa,xxb,on)
	return pw(phi([["M",xxa,y],["M",xxb,y]],[on]),phi([["M",xxb,y],["M",xxa,y]],iw([on])));
end;

phiznlist:=
[
#phizncheck(xa,xb,["C",y,xc]),
	applyrels(phizncheck(xa,xb,["C",y,xc]),[[1,krel(2,[xb,y^-1,xc^-1,xa,y^-1,xc^-1])]]),
phizncheck(xa,xb,["C",y,xa]),
phizncheck(xa,xb,["C",xc,y]),
phizncheck(xa,xb,["C",xa,y]),
phizncheck(xa,xb,["Mc",xc,y,xd]),
phizncheck(xa,xb,["Mc",xa,y,xd]),
phizncheck(xa,xb,["Mc",xc,y,xa]),
#phizncheck(xa,xb,["Mc",xa,y,xb]),
	applyrels(phizncheck(xa,xb,["Mc",xa,y,xb]),[[5,krel(1,[xb,xa])],[0,krel(1,[xa,xb])]])
];

# Verifying that a cancelling pair of generators in the second input in $\lambda$ gives a trivial output (with a generator or inverse generator in the first input).

lambda2ndinversecheck:=function(by,on)
	return lambda([by],[on,invertmove(on)]);
end;

lambda2ndinverselist:=
[
lambda2ndinversecheck(["I",xa],["M",xb,y]),
lambda2ndinversecheck(["I",xa],["M",xa,y]),

lambda2ndinversecheck(["I",xa],["M",xb,y^-1]),
lambda2ndinversecheck(["I",xa],["M",xa,y^-1]),

lambda2ndinversecheck(["P",xa,xb],["M",xc,y]),
lambda2ndinversecheck(["P",xa,xb],["M",xa,y]),
lambda2ndinversecheck(["P",xa,xb],["M",xc,y^-1]),
lambda2ndinversecheck(["P",xa,xb],["M",xa,y^-1]),

lambda2ndinversecheck(["M",xa,xb],["M",xc,y]),
#lambda2ndinversecheck(["M",xa,xb],["M",xa,y]),
	applyrels(lambda2ndinversecheck(["M",xa,xb],["M",xa,y]),[[3,iw(krel(6,[xa,y^-1,xb^-1]))]]),
#lambda2ndinversecheck(["M",xa,xb],["M",xb,y]),
	applyrels(lambda2ndinversecheck(["M",xa,xb],["M",xb,y]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),
lambda2ndinversecheck(["M",xa,xb],["M",xc,y^-1]),
#lambda2ndinversecheck(["M",xa,xb],["M",xa,y^-1]),
	applyrels(lambda2ndinversecheck(["M",xa,xb],["M",xa,y^-1]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),
#lambda2ndinversecheck(["M",xa,xb],["M",xb,y^-1]),
	applyrels(lambda2ndinversecheck(["M",xa,xb],["M",xb,y^-1]),[[3,iw(krel(6,[xa,y^-1,xb^-1]))]]),

lambda2ndinversecheck(["M",xa,xb^-1],["M",xc,y]),
#lambda2ndinversecheck(["M",xa,xb^-1],["M",xa,y]),
	applyrels(lambda2ndinversecheck(["M",xa,xb^-1],["M",xa,y]),[[3,iw(krel(6,[xa,y^-1,xb]))]]),
lambda2ndinversecheck(["M",xa,xb^-1],["M",xb,y]),
lambda2ndinversecheck(["M",xa,xb^-1],["M",xc,y^-1]),
#lambda2ndinversecheck(["M",xa,xb^-1],["M",xa,y^-1]),
	applyrels(lambda2ndinversecheck(["M",xa,xb^-1],["M",xa,y^-1]),[[3,iw(krel(6,[xa,y,xb]))]]),
lambda2ndinversecheck(["M",xa,xb^-1],["M",xb,y^-1]),

lambda2ndinversecheck(["M",xa^-1,xb],["M",xc,y]),
lambda2ndinversecheck(["M",xa^-1,xb],["M",xa,y]),
lambda2ndinversecheck(["M",xa^-1,xb],["M",xb,y]),
lambda2ndinversecheck(["M",xa^-1,xb],["M",xc,y^-1]),
lambda2ndinversecheck(["M",xa^-1,xb],["M",xa,y^-1]),
lambda2ndinversecheck(["M",xa^-1,xb],["M",xb,y^-1]),

lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xc,y]),
lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xa,y]),
lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xb,y]),
lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xc,y^-1]),
lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xa,y^-1]),
lambda2ndinversecheck(["M",xa^-1,xb^-1],["M",xb,y^-1]),
];

# verifying that basic commutators of generators in the second input to $\lambda$ gives a trivial output (with a generator or inverse generator in the first input).

lambda2ndrelcheck:=function(by,on1,on2)
	return lambda([by],commw([on1],[on2]));
end;

lambda2ndrellist:=
[
lambda2ndrelcheck(["I",xa],["M",xb,y],["M",xc,y]),
lambda2ndrelcheck(["I",xa],["M",xa,y],["M",xc,y]),

lambda2ndrelcheck(["P",xa,xb],["M",xc,y],["M",xd,y]),
lambda2ndrelcheck(["P",xa,xb],["M",xa,y],["M",xd,y]),
lambda2ndrelcheck(["P",xa,xb],["M",xa,y],["M",xb,y]),

lambda2ndrelcheck(["M",xa,xb],["M",xc,y],["M",xd,y]),
#lambda2ndrelcheck(["M",xa,xb],["M",xa,y],["M",xd,y]),
	applyrels(lambda2ndrelcheck(["M",xa,xb],["M",xa,y],["M",xd,y]),[[1,iw(krel(6,[xa,y,xb^-1]))]]),
#lambda2ndrelcheck(["M",xa,xb],["M",xb,y],["M",xd,y]),
	applyrels(lambda2ndrelcheck(["M",xa,xb],["M",xb,y],["M",xd,y]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),
#lambda2ndrelcheck(["M",xa,xb],["M",xa,y],["M",xb,y]),
	applyrels(lambda2ndrelcheck(["M",xa,xb],["M",xa,y],["M",xb,y]),[[5,iw(krel(6,[xa,y^-1,xb^-1]))],[3,iw(krel(6,[xa,y^-1,xb^-1]))]]),

lambda2ndrelcheck(["M",xa,xb^-1],["M",xc,y],["M",xd,y]),
#lambda2ndrelcheck(["M",xa,xb^-1],["M",xa,y],["M",xd,y]),
	applyrels(lambda2ndrelcheck(["M",xa,xb^-1],["M",xa,y],["M",xd,y]),[[3,iw(krel(6,[xa,y^-1,xb]))]]),
lambda2ndrelcheck(["M",xa,xb^-1],["M",xb,y],["M",xd,y]),
#lambda2ndrelcheck(["M",xa,xb^-1],["M",xa,y],["M",xb,y]),
	applyrels(lambda2ndrelcheck(["M",xa,xb^-1],["M",xa,y],["M",xb,y]),[[5,iw(krel(6,[xa,y^-1,xb]))],[3,krel(5,[xa,y,xb])],[1,iw(krel(6,[xa,y,xb]))]]),

lambda2ndrelcheck(["M",xa^-1,xb],["M",xc,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb],["M",xa,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb],["M",xb,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb],["M",xa,y],["M",xb,y]),

lambda2ndrelcheck(["M",xa^-1,xb^-1],["M",xc,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb^-1],["M",xa,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb^-1],["M",xb,y],["M",xd,y]),
lambda2ndrelcheck(["M",xa^-1,xb^-1],["M",xa,y],["M",xb,y]),
];

# Verifying the TB3 identity for $\lambda$ and $\phi$ for generators

tb3check:=function(sgen,zgen,kgen)
	return pw(cw(lambda([sgen],[zgen]),phi(psi([sgen],[zgen]),phi([sgen],[kgen]))),iw(phi([sgen],phi([zgen],[kgen]))));
end;

tb3list:=[
tb3check(["I",xa],["M",xb,y],["C",y,xc]), 
#tb3check(["I",xa],["M",xb,y],["C",y,xa]),
	applyrels(tb3check(["I",xa],["M",xb,y],["C",y,xa]),[[0,krel(4,[xb,y^-1,xa])]]),
tb3check(["I",xa],["M",xb,y],["C",y,xb]), 
tb3check(["I",xa],["M",xb,y],["C",xc,y]), 
tb3check(["I",xa],["M",xb,y],["C",xa,y]), 
tb3check(["I",xa],["M",xb,y],["C",xb,y]), 
tb3check(["I",xa],["M",xb,y],["Mc",xc,y,xd]), 
tb3check(["I",xa],["M",xb,y],["Mc",xa,y,xd]), 
tb3check(["I",xa],["M",xb,y],["Mc",xc,y,xa]), 
tb3check(["I",xa],["M",xb,y],["Mc",xb,y,xd]), 
tb3check(["I",xa],["M",xb,y],["Mc",xc,y,xb]), 
tb3check(["I",xa],["M",xb,y],["Mc",xa,y,xb]), 
tb3check(["I",xa],["M",xb,y],["Mc",xb,y,xa]), 
#tb3check(["I",xa],["M",xa,y],["C",y,xc]),
	applyrels(tb3check(["I",xa],["M",xa,y],["C",y,xc]),[[3,iw(krel(6,[xa,y^-1,xc^-1]))],[5,krel(7,[xa^-1,y^-1,xc^-1])]]),
tb3check(["I",xa],["M",xa,y],["C",y,xa]), 
#tb3check(["I",xa],["M",xa,y],["C",xc,y]),
	applyrels(tb3check(["I",xa],["M",xa,y],["C",xc,y]),[[0,krel(1,[xc,xa])]]),
tb3check(["I",xa],["M",xa,y],["C",xa,y]), 
#tb3check(["I",xa],["M",xa,y],["Mc",xc,y,xd]),
	applyrels(tb3check(["I",xa],["M",xa,y],["Mc",xc,y,xd]),[[3,krel(3,[xc,xd,y,xa])]]),
tb3check(["I",xa],["M",xa,y],["Mc",xa,y,xd]), 
tb3check(["I",xa],["M",xa,y],["Mc",xc,y,xa]), 

tb3check(["P",xa,xb],["M",xc,y],["C",y,xd]), 
tb3check(["P",xa,xb],["M",xc,y],["C",y,xa]), 
tb3check(["P",xa,xb],["M",xc,y],["C",y,xc]), 
tb3check(["P",xa,xb],["M",xc,y],["C",xd,y]), 
tb3check(["P",xa,xb],["M",xc,y],["C",xa,y]), 
tb3check(["P",xa,xb],["M",xc,y],["C",xc,y]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xd,y,xe]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xa,y,xe]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xd,y,xa]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xc,y,xe]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xd,y,xc]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xa,y,xb]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xa,y,xc]), 
tb3check(["P",xa,xb],["M",xc,y],["Mc",xc,y,xa]), 
tb3check(["P",xa,xb],["M",xa,y],["C",y,xd]), 
tb3check(["P",xa,xb],["M",xa,y],["C",y,xa]), 
tb3check(["P",xa,xb],["M",xa,y],["C",xd,y]), 
tb3check(["P",xa,xb],["M",xa,y],["C",xa,y]), 
tb3check(["P",xa,xb],["M",xa,y],["Mc",xd,y,xe]), 
tb3check(["P",xa,xb],["M",xa,y],["Mc",xa,y,xe]), 
tb3check(["P",xa,xb],["M",xa,y],["Mc",xd,y,xa]), 
tb3check(["P",xa,xb],["M",xa,y],["Mc",xa,y,xb]), 
tb3check(["P",xa,xb],["M",xa,y],["Mc",xb,y,xa]), 

tb3check(["M",xa,xb],["M",xc,y],["C",y,xd]), 
#tb3check(["M",xa,xb],["M",xc,y],["C",y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["C",y,xa]),[[4,iw(krel(4,[xc,y^-1,xb]))]]),
tb3check(["M",xa,xb],["M",xc,y],["C",y,xb]), 
tb3check(["M",xa,xb],["M",xc,y],["C",y,xc]), 
tb3check(["M",xa,xb],["M",xc,y],["C",xd,y]), 
tb3check(["M",xa,xb],["M",xc,y],["C",xa,y]), 
tb3check(["M",xa,xb],["M",xc,y],["C",xb,y]), 
tb3check(["M",xa,xb],["M",xc,y],["C",xc,y]), 
tb3check(["M",xa,xb],["M",xc,y],["Mc",xd,y,xe]), 
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xa,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xa,y,xe]),[[1,krel(2,[xa,y,xb^-1,xc,y^-1,xe^-1])]]),
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xd,y,xa]),[[1,krel(2,[xd,y,xb,xc,y^-1,xa^-1])]]),
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xb,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xb,y,xe]),[[4,krel(2,[xa,xb^-1,y,xc,y^-1,xe^-1])]]),
tb3check(["M",xa,xb],["M",xc,y],["Mc",xd,y,xb]), 
tb3check(["M",xa,xb],["M",xc,y],["Mc",xc,y,xe]), 
tb3check(["M",xa,xb],["M",xc,y],["Mc",xd,y,xc]), 
tb3check(["M",xa,xb],["M",xc,y],["Mc",xa,y,xb]), 
tb3check(["M",xa,xb],["M",xc,y],["Mc",xb,y,xa]), 
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xa,y,xc]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xa,y,xc]),[[6,krel(3,[xa,xb^-1,y,xc])]]),
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xc,y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xc,y,xa]),[[2,iw(krel(6,[xc,y,xb]))],[4,krel(7,[xc,y^-1,xa^-1])],[2,krel(2,[xc^-1,y^-1,xa^-1,xc,xb,y^-1])],[3,krel(6,[xc,y,xb])],[1,iw(krel(7,[xc,y^-1,xa^-1]))]]),
#tb3check(["M",xa,xb],["M",xc,y],["Mc",xb,y,xc]),
	applyrels(tb3check(["M",xa,xb],["M",xc,y],["Mc",xb,y,xc]),[[3,krel(3,[xa,y,xb^-1,xc])]]),
tb3check(["M",xa,xb],["M",xc,y],["Mc",xc,y,xb]), 

tb3check(["M",xa^-1,xb],["M",xc,y],["C",y,xd]), 
#tb3check(["M",xa^-1,xb],["M",xc,y],["C",y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xc,y],["C",y,xa]),[[4,krel(4,[xc,y^-1,xb])]]),
tb3check(["M",xa^-1,xb],["M",xc,y],["C",y,xb]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["C",y,xc]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["C",xd,y]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["C",xa,y]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["C",xb,y]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["C",xc,y]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xd,y,xe]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xa,y,xe]), 
#tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xd,y,xa]),[[6,iw(krel(4,[xc,y^-1,xb]))],[3,krel(2,[xc,xb,y^-1,xd,xb,y])],[2,krel(2,[xc,xb,y^-1,xd,y,xa])],[0,krel(4,[xc,y^-1,xb])]]),
#tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xe]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xe]),[[4,krel(2,[xa^-1,xb^-1,y,xc,y^-1,xe^-1])]]),
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xd,y,xb]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xc,y,xe]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xd,y,xc]), 
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xa,y,xb]), 
#tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xa]),
	tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xa^-1]),
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xa,y,xc]), 
#tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xc,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xc,y,xa]),[[1,krel(7,[xc,y^-1,xb^-1])],[1,iw(krel(6,[xc^-1,y,xb^-1]))],[3,krel(4,[xc^-1,y,xb^-1])],[2,krel(2,[xc,y,xa,xc^-1,y,xb])],[3,krel(2,[xc,xb,y,xc^-1,y,xb])],[6,iw(krel(4,[xc,y^-1,xb^-1]))],[6,krel(6,[xc,y,xb])],[4,iw(krel(7,[xc^-1,y,xb]))]]),
#tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xc]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xb,y,xc]),[[3,krel(3,[xa^-1,y,xb^-1,xc])]]),
tb3check(["M",xa^-1,xb],["M",xc,y],["Mc",xc,y,xb]), 

tb3check(["M",xa,xb],["M",xa,y],["C",y,xd]), 
#tb3check(["M",xa,xb],["M",xa,y],["C",y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["C",y,xa]),[[1,iw(krel(6,[xa,y,xb^-1]))]]),
tb3check(["M",xa,xb],["M",xa,y],["C",y,xb]), 
#tb3check(["M",xa,xb],["M",xa,y],["C",xd,y]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["C",xd,y]),[[0,krel(3,[xa,y^-1,xb^-1,xd])]]),
#tb3check(["M",xa,xb],["M",xa,y],["C",xa,y]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["C",xa,y]),[[5,krel(6,[xa,y,xb^-1])],[1,iw(krel(6,[xa,y,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["C",xb,y]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["C",xb,y]),[[5,iw(exkrel(1,[xa,y^-1,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xe]),[[0,krel(2,[xd,y,xe,xa,y^-1,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xa,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xa,y,xe]),[[14,krel(6,[xa,y^-1,xb^-1])],[7,krel(7,[xa,y^-1,xe^-1])],[5,iw(krel(6,[xa^-1,y^-1,xe^-1]))],[4,krel(2,[xa^-1,xe^-1,y,xa,y,xb^-1])],[4,krel(6,[xa^-1,y^-1,xe^-1])],[2,iw(krel(7,[xa,y^-1,xe^-1]))],[1,iw(krel(6,[xa,y,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xa]),[[7,krel(6,[xa,y,xb^-1])],[1,iw(krel(6,[xa,y,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xb,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xb,y,xe]),[[2,cyw(-3,iw(exkrel(7,[xa,y^-1,xb^-1,xe])))],[16,krel(6,[xa,y,xe])],[18,iw(krel(4,[xa,y^-1,xe]))],[9,krel(4,[xa,y^-1,xe])],[19,krel(6,[xa,y,xb^-1])],[12,iw(krel(6,[xa,y,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xb]),   	96
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xd,y,xb]),[[0,krel(2,[xd,y,xb,xa,y^-1,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xa,y,xb]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xa,y,xb]),[[6,krel(6,[xa,y^-1,xb^-1])],[3,iw(krel(6,[xa,y^-1,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xa,y],["Mc",xb,y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xa,y],["Mc",xb,y,xa]),[[1,iw(krel(6,[xa,y,xb^-1]))],[4,krel(1,[xa,xb])],[9,krel(6,[xa,y^-1,xb^-1])]]),

tb3check(["M",xa^-1,xb],["M",xa,y],["C",y,xd]), 
#tb3check(["M",xa^-1,xb],["M",xa,y],["C",y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["C",y,xa]),[[5,iw(krel(6,[xa^-1,y^-1,xb^-1]))],[1,krel(7,[xa,y^-1,xb^-1])]]),
tb3check(["M",xa^-1,xb],["M",xa,y],["C",y,xb]), 
tb3check(["M",xa^-1,xb],["M",xa,y],["C",xd,y]), 
tb3check(["M",xa^-1,xb],["M",xa,y],["C",xa,y]), 
tb3check(["M",xa^-1,xb],["M",xa,y],["C",xb,y]), 
tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xd,y,xe]), 
#tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xa,y,xe]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xa,y,xe]),[[1,krel(2,[xa^-1,xb^-1,y,xa,y,xe])]]),
#tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xd,y,xa]),[[8,iw(krel(6,[xa,y,xb^-1]))],[10,krel(7,[xa^-1,y,xb^-1])],[5,krel(3,[xd,xb,y,xa])],[5,iw(krel(6,[xa^-1,y^-1,xb^-1]))],[1,krel(7,[xa,y^-1,xb^-1])]]),
#tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xb,y,xe]),			
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xb,y,xe]),[[4,krel(2,[xa^-1,xb^-1,y,xa,y^-1,xe^-1])]]),
tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xd,y,xb]), 
#tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xa,y,xb]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xa,y,xb]),[[1,krel(2,[xa^-1,xb^-1,y,xa,y,xb])]]),
#tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xb,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xa,y],["Mc",xb,y,xa]),[[1,krel(7,[xa,y^-1,xb^-1])],[1,iw(krel(6,[xa^-1,y,xb^-1]))],[12,iw(krel(6,[xa,y,xb^-1]))],[14,krel(7,[xa^-1,y,xb^-1])]]),

#tb3check(["M",xa,xb],["M",xb,y],["C",y,xd]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["C",y,xd]),[[1,iw(krel(4,[xb,y^-1,xd^-1]))],[0,cyw(-1,iw(exkrel(8,[xa,y,xb^-1,xd])))],[2,krel(4,[xb,y^-1,xd])],[15,iw(krel(4,[xa,y^-1,xd^-1]))],[10,iw(krel(4,[xa,y,xd^-1]))]]),
#tb3check(["M",xa,xb],["M",xb,y],["C",y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["C",y,xa]),[[1,iw(krel(6,[xa,y^-1,xb^-1]))],[4,iw(krel(6,[xb,y,xa^-1]))],[6,krel(4,[xb,y,xa^-1])],[5,iw(krel(7,[xb,y,xa]))]]),
#tb3check(["M",xa,xb],["M",xb,y],["C",y,xb]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["C",y,xb]),[[3,iw(krel(5,[xa,y,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xb,y],["C",xd,y]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["C",xd,y]),[[0,krel(3,[xa,y,xb^-1,xd])]]),
tb3check(["M",xa,xb],["M",xb,y],["C",xa,y]), 
#tb3check(["M",xa,xb],["M",xb,y],["C",xb,y]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["C",xb,y]),[[5,krel(6,[xa,y^-1,xb^-1])],[1,iw(krel(5,[xa,y^-1,xb^-1]))]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xe]),[[0,krel(2,[xd,y,xe,xa,y,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xa,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xa^-1,y,xe]),[[0,krel(2,[xa^-1,y,xe,xa,y,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xa^-1]),[[2,krel(3,[xd,y,xa^-1,xb])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xb,y,xe]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xb^-1,y,xe]),[[2,cyw(-3,iw(exkrel(3,[xa,y,xb^-1,xe])))],[6,exkrel(1,[xa,y,xe])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xb]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xd,y,xb^-1]),[[0,krel(2,[xd,y,xb^-1,xa,y,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xa,y,xb]),
	applyrels(tb3check(["M",xa,xb],["M",xb,y],["Mc",xa^-1,y,xb^-1]),[[0,krel(2,[xa^-1,y,xb^-1,xa,y,xb^-1])]]),
#tb3check(["M",xa,xb],["M",xb,y],["Mc",xb,y,xa]),

#tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xd]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xd]),[[2,iw(krel(4,[xb,y^-1,xd^-1]))],[2,krel(3,[xb,xd,y^-1,xa])],[2,cyw(-3,iw(exkrel(8,[xa^-1,y,xb^-1,xd])))],[2,krel(4,[xb,y^-1,xd])],[5,iw(krel(4,[xa^-1,y^-1,xd^-1]))],[11,iw(krel(4,[xa,y^-1,xd^-1]))],[11,krel(6,[xa,y,xd])],[9,iw(krel(7,[xa^-1,y,xd]))]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xa]),[[1,iw(krel(6,[xa^-1,y^-1,xb^-1]))],[3,krel(7,[xa,y^-1,xb^-1])],[9,krel(6,[xa^-1,y,xb^-1])],[6,iw(krel(6,[xb,y,xa^-1]))],[8,krel(7,[xb^-1,y,xa^-1])],[3,krel(1,[xb,xa])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xb]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["C",y,xb]),[[9,iw(krel(5,[xa^-1,y,xb^-1]))],[5,iw(krel(6,[xa,y,xb^-1]))],[7,krel(7,[xa^-1,y,xb^-1])],[2,krel(1,[xa,xb])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["C",xd,y]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["C",xd,y]),[[2,krel(1,[xa,xd])],[0,krel(3,[xa^-1,y,xb^-1,xd])]]),
tb3check(["M",xa^-1,xb],["M",xb,y],["C",xa,y]),  
#tb3check(["M",xa^-1,xb],["M",xb,y],["C",xb,y]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["C",xb,y]),[[7,iw(krel(5,[xa^-1,y,xb^-1]))],[3,krel(6,[xa^-1,y,xb^-1])],[2,krel(1,[xa,xb])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xe]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xe]),[[2,krel(3,[xd,y,xe,xa])],[0,krel(2,[xd,y,xe,xa^-1,y,xb^-1])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xa,y,xe]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xa,y,xe]),[[0,krel(2,[xa,y,xe,xa^-1,y,xb^-1])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xa]),[[1,iw(krel(6,[xa^-1,y^-1,xb^-1]))],[3,krel(7,[xa,y^-1,xb^-1])],[3,krel(1,[xb,xa])],[2,krel(3,[xd,y,xa,xb])],[4,krel(1,[xa,xb])],[3,krel(3,[xd,xb,y,xa])],[6,iw(krel(6,[xa,y,xb^-1]))],[8,krel(7,[xa^-1,y,xb^-1])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xb,y,xe]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xb^-1,y,xe]),[[2,krel(3,[xb^-1,y,xe,xa])],[2,cyw(-3,iw(exkrel(3,[xa^-1,y,xb^-1,xe])))],[6,exkrel(1,[xa^-1,y,xe])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xb]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xd,y,xb^-1]),[[2,krel(3,[xd,y,xb^-1,xa])],[0,krel(2,[xd,y,xb^-1,xa^-1,y,xb^-1])]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xa,y,xb]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xa,y,xb]),[[6,krel(2,[xa,xb,y,xa^-1,xb^-1,y^-1])],[4,krel(5,[xa^-1,y^-1,xb^-1])],[2,krel(2,[xa^-1,y^-1,xb^-1,xa,y,xb])],[1,iw(krel(5,[xa^-1,y^-1,xb^-1]))]]),
#tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xb,y,xa]),
	applyrels(tb3check(["M",xa^-1,xb],["M",xb,y],["Mc",xb,y,xa^-1]),[[11,iw(krel(5,[xa^-1,y,xb^-1]))],[5,krel(6,[xa^-1,y,xb^-1])],[4,krel(1,[xa,xb])],[3,krel(1,[xa,xb])],[1,iw(exkrel(1,[xb^-1,y^-1,xa^-1]))]])
];

# verifying that a cancelling pair of generators in the first input (and a positive generator in the second input) gives a trivial output for $\lambda$.

lambda1stinversecheck:=function(by,on)
	return lambda([by,invertmove(by)],[on]);
end;

lambda1stinverselist:=
[
lambda1stinversecheck(["I",xa],["M",xb,y]),
lambda1stinversecheck(["I",xa],["M",xa,y]),

lambda1stinversecheck(["P",xa,xb],["M",xc,y]),
lambda1stinversecheck(["P",xa,xb],["M",xa,y]),

lambda1stinversecheck(["M",xa,xb],["M",xc,y]),
lambda1stinversecheck(["M",xa,xb],["M",xa,y]),
#lambda1stinversecheck(["M",xa,xb],["M",xb,y]),
	applyrels(lambda1stinversecheck(["M",xa,xb],["M",xb,y]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),

lambda1stinversecheck(["M",xa^-1,xb],["M",xc,y]),
lambda1stinversecheck(["M",xa^-1,xb],["M",xa,y]),
lambda1stinversecheck(["M",xa^-1,xb],["M",xb,y]),

lambda1stinversecheck(["M",xa,xb^-1],["M",xc,y]),
lambda1stinversecheck(["M",xa,xb^-1],["M",xa,y]),
#lambda1stinversecheck(["M",xa,xb^-1],["M",xb,y]),
	applyrels(lambda1stinversecheck(["M",xa,xb^-1],["M",xb,y]),[[2,iw(exkrel(1,[xa,y,xb]))]]),

lambda1stinversecheck(["M",xa^-1,xb^-1],["M",xc,y]),
lambda1stinversecheck(["M",xa^-1,xb^-1],["M",xa,y]),
lambda1stinversecheck(["M",xa^-1,xb^-1],["M",xb,y]),
];

# Verifying that Nielsen's relations in the first input and a generator in the second input gives trivial output for $\lambda$.

lambdaN1list:=
[
lambda([["I",xa],["I",xa]],[["M",xb,y]]),
lambda([["I",xa],["I",xa]],[["M",xa,y]]),

lambda(commw([["I",xa]],[["I",xb]]),[["M",xc,y]]),
lambda(commw([["I",xa]],[["I",xb]]),[["M",xa,y]]),
lambda(commw([["I",xa]],[["I",xb]]),[["M",xb,y]]),

lambda([["P",xa,xb],["P",xa,xb]],[["M",xa,y]]),
lambda([["P",xa,xb],["P",xa,xb]],[["M",xc,y]]),

lambda(commw([["P",xa,xb]],[["P",xc,xd]]),[["M",xe,y]]),
lambda(commw([["P",xa,xb]],[["P",xc,xd]]),[["M",xa,y]]),
lambda(commw([["P",xa,xb]],[["P",xc,xd]]),[["M",xc,y]]),

lambda([["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc]],[["M",xd,y]]),
lambda([["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc]],[["M",xa,y]]),
lambda([["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc]],[["M",xb,y]]),
lambda([["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc],["P",xa,xb],["P",xb,xc]],[["M",xc,y]]),

lambda([["P",xa,xb],["I",xa],["P",xa,xb],["I",xb]],[["M",xc,y]]),
lambda([["P",xa,xb],["I",xa],["P",xa,xb],["I",xb]],[["M",xa,y]]),
lambda([["P",xa,xb],["I",xa],["P",xa,xb],["I",xb]],[["M",xb,y]]),

lambda(commw([["P",xa,xb]],[["I",xc]]),[["M",xd,y]]),
lambda(commw([["P",xa,xb]],[["I",xc]]),[["M",xa,y]]),
lambda(commw([["P",xa,xb]],[["I",xc]]),[["M",xc,y]]),
];

lambdaN2list:=
[
lambda(commw([["I",xa]],[["M",xb,xc]]),[["M",xd,y]]), 
lambda(commw([["I",xa]],[["M",xb,xc]]),[["M",xa,y]]), 
lambda(commw([["I",xa]],[["M",xb,xc]]),[["M",xb,y]]),
#lambda(commw([["I",xa]],[["M",xb,xc]]),[["M",xc,y]]), 
	applyrels(lambda(commw([["I",xa]],[["M",xb,xc]]),[["M",xc,y]]),[[3,iw(krel(6,[xb,y,xc^-1]))]]),

lambda(commw([["I",xa]],[["M",xb^-1,xc]]),[["M",xd,y]]),
lambda(commw([["I",xa]],[["M",xb^-1,xc]]),[["M",xa,y]]),
lambda(commw([["I",xa]],[["M",xb^-1,xc]]),[["M",xb,y]]),
lambda(commw([["I",xa]],[["M",xb^-1,xc]]),[["M",xc,y]]),

lambda([["I",xa],["M",xb,xa],["I",xa],["M",xb,xa]],[["M",xc,y]]),
#lambda([["I",xa],["M",xb,xa],["I",xa],["M",xb,xa]],[["M",xa,y]]),
	applyrels(lambda([["I",xa],["M",xb,xa],["I",xa],["M",xb,xa]],[["M",xa,y]]),[[4,iw(krel(6,[xb,y^-1,xa]))],[2,krel(5,[xb,y,xa])]]),
lambda([["I",xa],["M",xb,xa],["I",xa],["M",xb,xa]],[["M",xb,y]]),

lambda([["I",xa],["M",xb^-1,xa],["I",xa],["M",xb^-1,xa]],[["M",xc,y]]),
#lambda([["I",xa],["M",xb^-1,xa],["I",xa],["M",xb^-1,xa]],[["M",xa,y]]),
	applyrels(lambda([["I",xa],["M",xb^-1,xa],["I",xa],["M",xb^-1,xa]],[["M",xa,y]]),[[2,krel(6,[xb^-1,y,xa])],[1,krel(1,[xb,xa])]]),
lambda([["I",xa],["M",xb^-1,xa],["I",xa],["M",xb^-1,xa]],[["M",xb,y]]),

lambda([["I",xa],["M",xa,xb],["I",xa],["M",xa^-1,xb^-1]],[["M",xc,y]]),
lambda([["I",xa],["M",xa,xb],["I",xa],["M",xa^-1,xb^-1]],[["M",xa,y]]),
#lambda([["I",xa],["M",xa,xb],["I",xa],["M",xa^-1,xb^-1]],[["M",xb,y]]),
	applyrels(lambda([["I",xa],["M",xa,xb],["I",xa],["M",xa^-1,xb^-1]],[["M",xb,y]]),[[3,iw(krel(6,[xa^-1,y,xb^-1]))]]),

lambda(commw([["P",xa,xb]],[["M",xc,xd]]),[["M",xe,y]]),
lambda(commw([["P",xa,xb]],[["M",xc,xd]]),[["M",xa,y]]),
lambda(commw([["P",xa,xb]],[["M",xc,xd]]),[["M",xc,y]]),
#lambda(commw([["P",xa,xb]],[["M",xc,xd]]),[["M",xd,y]]),
	applyrels(lambda(commw([["P",xa,xb]],[["M",xc,xd]]),[["M",xd,y]]),[[3,iw(krel(6,[xc,y,xd^-1]))]]),

lambda(commw([["P",xa,xb]],[["M",xc^-1,xd]]),[["M",xe,y]]),
lambda(commw([["P",xa,xb]],[["M",xc^-1,xd]]),[["M",xa,y]]),
lambda(commw([["P",xa,xb]],[["M",xc^-1,xd]]),[["M",xc,y]]),
lambda(commw([["P",xa,xb]],[["M",xc^-1,xd]]),[["M",xd,y]]),

lambda([["P",xa,xb],["M",xa,xc],["P",xa,xb],["M",xb,xc^-1]],[["M",xd,y]]),
lambda([["P",xa,xb],["M",xa,xc],["P",xa,xb],["M",xb,xc^-1]],[["M",xa,y]]),
lambda([["P",xa,xb],["M",xa,xc],["P",xa,xb],["M",xb,xc^-1]],[["M",xb,y]]),
#lambda([["P",xa,xb],["M",xa,xc],["P",xa,xb],["M",xb,xc^-1]],[["M",xc,y]]),
	applyrels(lambda([["P",xa,xb],["M",xa,xc],["P",xa,xb],["M",xb,xc^-1]],[["M",xc,y]]),[[3,iw(krel(6,[xb,y,xc^-1]))]]),

lambda([["P",xa,xb],["M",xa^-1,xc],["P",xa,xb],["M",xb^-1,xc^-1]],[["M",xd,y]]),
lambda([["P",xa,xb],["M",xa^-1,xc],["P",xa,xb],["M",xb^-1,xc^-1]],[["M",xa,y]]),
lambda([["P",xa,xb],["M",xa^-1,xc],["P",xa,xb],["M",xb^-1,xc^-1]],[["M",xb,y]]),
lambda([["P",xa,xb],["M",xa^-1,xc],["P",xa,xb],["M",xb^-1,xc^-1]],[["M",xc,y]]),

lambda([["P",xa,xb],["M",xc,xa],["P",xa,xb],["M",xc,xb^-1]],[["M",xd,y]]),
lambda([["P",xa,xb],["M",xc,xa],["P",xa,xb],["M",xc,xb^-1]],[["M",xa,y]]),
#lambda([["P",xa,xb],["M",xc,xa],["P",xa,xb],["M",xc,xb^-1]],[["M",xb,y]]),
	applyrels(lambda([["P",xa,xb],["M",xc,xa],["P",xa,xb],["M",xc,xb^-1]],[["M",xb,y]]),[[3,iw(krel(6,[xc,y,xb^-1]))]]),
lambda([["P",xa,xb],["M",xc,xa],["P",xa,xb],["M",xc,xb^-1]],[["M",xc,y]]),

lambda([["P",xa,xb],["M",xc^-1,xa],["P",xa,xb],["M",xc^-1,xb^-1]],[["M",xd,y]]),
lambda([["P",xa,xb],["M",xc^-1,xa],["P",xa,xb],["M",xc^-1,xb^-1]],[["M",xa,y]]),
lambda([["P",xa,xb],["M",xc^-1,xa],["P",xa,xb],["M",xc^-1,xb^-1]],[["M",xb,y]]),
lambda([["P",xa,xb],["M",xc^-1,xa],["P",xa,xb],["M",xc^-1,xb^-1]],[["M",xc,y]]),

lambda([["P",xa,xb],["M",xa,xb],["P",xa,xb],["M",xb,xa^-1]],[["M",xc,y]]),
#lambda([["P",xa,xb],["M",xa,xb],["P",xa,xb],["M",xb,xa^-1]],[["M",xa,y]]),
	applyrels(lambda([["P",xa,xb],["M",xa,xb],["P",xa,xb],["M",xb,xa^-1]],[["M",xa,y]]),[[3,iw(krel(6,[xb,y,xa^-1]))]]),
lambda([["P",xa,xb],["M",xa,xb],["P",xa,xb],["M",xb,xa^-1]],[["M",xb,y]]),

lambda([["P",xa,xb],["M",xa^-1,xb],["P",xa,xb],["M",xb^-1,xa^-1]],[["M",xc,y]]),
lambda([["P",xa,xb],["M",xa^-1,xb],["P",xa,xb],["M",xb^-1,xa^-1]],[["M",xa,y]]),
lambda([["P",xa,xb],["M",xa^-1,xb],["P",xa,xb],["M",xb^-1,xa^-1]],[["M",xb,y]]),
];

lambdaN3list:=[
lambda([["P",xa,xb],["I",xb],["M",xa^-1,xb],["M",xb,xa],["M",xa,xb^-1]],[["M",xc,y]]),
#lambda([["P",xa,xb],["I",xb],["M",xa^-1,xb],["M",xb,xa],["M",xa,xb^-1]],[["M",xa,y]]),
	applyrels(lambda([["P",xa,xb],["I",xb],["M",xa^-1,xb],["M",xb,xa],["M",xa,xb^-1]],[["M",xa,y]]),[[6,krel(5,[xb^-1,y,xa])],[4,iw(krel(6,[xb^-1,y,xa]))],[3,krel(1,[xa,xb])],[0,iw(krel(5,[xa,y,xb^-1]))]]),
#lambda([["P",xa,xb],["I",xb],["M",xa^-1,xb],["M",xb,xa],["M",xa,xb^-1]],[["M",xb,y]]),
	applyrels(lambda([["P",xa,xb],["I",xb],["M",xa^-1,xb],["M",xb,xa],["M",xa,xb^-1]],[["M",xb,y]]),[[11,iw(krel(6,[xb^-1,y,xa]))],[3,iw(krel(6,[xb^-1,y,xa]))],[5,krel(5,[xb^-1,y,xa])],[2,krel(1,[xa,xb])],[3,iw(krel(5,[xa,y,xb^-1]))],[0,krel(1,[xa,xb])]]),
];

lambdaN4list:=
[
lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xe,y]]), 
lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xa,y]]),
#lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xb,y]]),
	applyrels(lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xb,y]]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),
lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xc,y]]),
#lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xd,y]]),
	applyrels(lambda(commw([["M",xa,xb]],[["M",xc,xd]]),[["M",xd,y]]),[[3,iw(krel(6,[xc,y,xd^-1]))]]),

lambda(commw([["M",xa,xb]],[["M",xc,xb]]),[["M",xe,y]]),
lambda(commw([["M",xa,xb]],[["M",xc,xb]]),[["M",xa,y]]),
#lambda(commw([["M",xa,xb]],[["M",xc,xb]]),[["M",xb,y]]),
	applyrels(lambda(commw([["M",xa,xb]],[["M",xc,xb]]),[["M",xb,y]]),[[7,iw(krel(6,[xa,y,xb^-1]))],[3,iw(krel(6,[xc,y,xb^-1]))]]),
lambda(commw([["M",xa,xb]],[["M",xc,xb]]),[["M",xc,y]]),

lambda(commw([["M",xa,xb]],[["M",xa^-1,xd]]),[["M",xe,y]]),
lambda(commw([["M",xa,xb]],[["M",xa^-1,xd]]),[["M",xa,y]]),
#lambda(commw([["M",xa,xb]],[["M",xa^-1,xd]]),[["M",xb,y]]),
	applyrels(lambda(commw([["M",xa,xb]],[["M",xa^-1,xd]]),[["M",xb,y]]),[[3,iw(krel(6,[xa,y,xb^-1]))]]),
lambda(commw([["M",xa,xb]],[["M",xa^-1,xd]]),[["M",xd,y]]),

lambda(commw([["M",xa,xb]],[["M",xa^-1,xb]]),[["M",xe,y]]),
lambda(commw([["M",xa,xb]],[["M",xa^-1,xb]]),[["M",xa,y]]),
#lambda(commw([["M",xa,xb]],[["M",xa^-1,xb]]),[["M",xb,y]]),
	applyrels(lambda(commw([["M",xa,xb]],[["M",xa^-1,xb]]),[["M",xb,y]]),[[9,krel(2,[xa,xb^-1,y,xa^-1,xb^-1,y^-1])],[8,krel(5,[xa,y,xb^-1])],[11,iw(krel(5,[xa,y,xb^-1]))],[11,exkrel(1,[xa,y,xb^-1])],[5,krel(2,[xa^-1,xb^-1,y,xa,xb^-1,y])],[5,krel(6,[xa^-1,y^-1,xb^-1])],[7,krel(2,[xa^-1,y,xb^-1,xa,xb^-1,y])],[8,iw(krel(6,[xa^-1,y^-1,xb^-1]))],[3,krel(2,[xa^-1,y^-1,xb^-1,xa,y,xb^-1])],[3,iw(krel(6,[xa,y,xb^-1]))]]),

];

lambdaN5list:=
[
lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xd,y]]),
#lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xa,y]]),
	applyrels(lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xa,y]]),[[0,iw(krel(4,[xc,y,xa^-1]))],[4,krel(4,[xc,y,xa])],[1,krel(2,[xb,xa,y,xc,xa,y])],[3,krel(4,[xc,y^-1,xa])],[3,krel(6,[xc,y,xb])],[5,krel(4,[xc,y,xa])],[5,iw(krel(6,[xc,y^-1,xa]))],[3,krel(5,[xc,y,xb])],[4,iw(exkrel(1,[xb,y,xa]))],[1,iw(exkrel(3,[xc,y,xb,xa]))],[4,krel(1,[xa,xb])],[2,krel(3,[xc,xa,y,xb])],[1,krel(1,[xb,xa])],[3,iw(krel(5,[xc,y,xb]))]]),
#lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xb,y]]),
	applyrels(lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xb,y]]),[[10,iw(exkrel(1,[xc,y,xb]))],[7,krel(2,[xc,y^-1,xa,xb,y^-1,xa])],[0,krel(2,[xb,xa,y^-1,xc,xa,y^-1])],[8,iw(krel(8,[xc,y,xb,xa]))],[4,krel(4,[xc,y,xa])],[3,krel(4,[xc,y^-1,xa])]]),
lambda([["M",xc,xb^-1],["M",xb,xa^-1],["M",xc,xb],["M",xb,xa],["M",xc,xa]],[["M",xc,y]]),
];

# Verifying that the defining relations for $\Gamma_n$ correspond to true equations in $\Aut(F_n)$.

verifyGammarellist:=
[
checkpair([krel(1,[xa,xb]),[]]),

checkpair([krel(2,[xa,y,xb,xc,y,xd]),[]]),
checkpair([krel(2,[xa,y,xb,xc,y,xb]),[]]),
checkpair([krel(2,[xa,y,xb,xc,y,xb^-1]),[]]),
checkpair([krel(2,[xa,y,xb,xa^-1,y,xd]),[]]),
checkpair([krel(2,[xa,y,xb,xa^-1,y,xb]),[]]),
checkpair([krel(2,[xa,y,xb,xa^-1,y,xb^-1]),[]]),

checkpair([krel(2,[xa,y^-1,xb,xc,y,xd]),[]]),
checkpair([krel(2,[xa,y^-1,xb,xc,y,xb]),[]]),
checkpair([krel(2,[xa,y^-1,xb,xc,y,xb^-1]),[]]),
checkpair([krel(2,[xa,y^-1,xb,xa^-1,y,xd]),[]]),
checkpair([krel(2,[xa,y^-1,xb,xa^-1,y,xb]),[]]),
checkpair([krel(2,[xa,y^-1,xb,xa^-1,y,xb^-1]),[]]),

checkpair([krel(3,[xa,y,xb,xc]),[]]),

checkpair([krel(4,[xa,y,xb]),[]]),

checkpair([krel(5,[xa,y,xb]),[]]),

checkpair([krel(6,[xa,y,xb]),[]]),

checkpair([krel(7,[xa,y,xb]),[]]),

checkpair([krel(8,[xa,y,xb,xc]),[]]),

checkpair([krel(9,[xa,y,xb,xc]),[]]),

checkpair([krel(10,[xa,y,xb,xc]),[]]),
];

# The following three functions produce relations from the presentation $\Delta$.

znrel:=function(xxa,xxb)
	return commw([["M",xxa,y]],[["M",xxb,y]]);
end;

dphirel:=function(by,on)
	return pw(phi([by],[on]),[by],iw([on]),iw([by]));
end;

dpsirel:=function(by,on)
	return pw(lambda([by],[on]),psi([by],[on]),[by],iw([on]),iw([by]));
end;


# Verifying that the relations in Jensen--Wahl's presentation for the conjugacy stabilizer of a basis element in $\Aut(F_n)$ follow from the relations for $\Delta_n$.

JWfromDeltalist:= [
#Q2 relations
#commw([["M",xa,y]],[["M",xb,y]])
	applyrels(commw([["M",xa,y]],[["M",xb,y]]),[[0,znrel(xb,xa)]]),
#commw([["C",xa,y],["M",xa,y^-1]],[["M",xb,y]])
	applyrels(commw([["C",xa,y],["M",xa,y^-1]],[["M",xb,y]]),[[2,znrel(xa,xb)],[0,iw(dphirel(["M",xb,y],["C",xa,y]))]]),
#commw([["C",xa,y],["M",xa,y^-1]],[["M",xa,y]])
	applyrels(commw([["C",xa,y],["M",xa,y^-1]],[["M",xa,y]]),[[0,iw(dphirel(["M",xa,y],["C",xa,y]))]]),
#commw([["C",xa,y],["M",xa,y^-1]],[["C",xb,y],["M",xb,y^-1]])
	applyrels(commw([["C",xa,y],["M",xa,y^-1]],[["C",xb,y],["M",xb,y^-1]]),[[3,dphirel(["M",xa,y],["C",xb,y^-1])],[4,znrel(xb,xa)],[4,dphirel(["M",xb,y],["C",xa,y])],[0,krel(1,[xb,xa])]]),
#commw([["M",xa,xb]],[["M",xc,y]])
	applyrels(commw([["M",xa,xb]],[["M",xc,y]]),[[0,dpsirel(["M",xa,xb],["M",xc,y])]]),
#commw([["M",xa,xb]],[["C",xc,y],["M",xc,y^-1]])
	applyrels(commw([["M",xa,xb]],[["C",xc,y],["M",xc,y^-1]]),[[5,dpsirel(["M",xa,xb],["M",xc,y^-1])],[0,dphirel(["M",xa,xb],["C",xc,y])]]),
#commw([["M",xa,xb]],[["C",xa,y],["M",xa,y^-1]])
	applyrels(commw([["M",xa,xb]],[["C",xa,y],["M",xa,y^-1]]),[[0,dphirel(["M",xa,xb],["C",xa,y])],[2,dpsirel(["M",xa,xb],["M",xa,y^-1])]]),
#commw([["M",xa,xb]],[["C",y,xc]])
	applyrels(commw([["M",xa,xb]],[["C",y,xc]]),[[0,dphirel(["M",xa,xb],["C",y,xc])]]),

#Q3 Relations
#[["P",xa,xb],["C",y,xc],["P",xa,xb],["C",y,xc^-1]],
	applyrels([["P",xa,xb],["C",y,xc],["P",xa,xb],["C",y,xc^-1]],[[0,dphirel(["P",xa,xb],["C",y,xc])]]),
#[["P",xa,xb],["C",y,xa],["P",xa,xb],["C",y,xb^-1]],
	applyrels([["P",xa,xb],["C",y,xa],["P",xa,xb],["C",y,xb^-1]],[[0,dphirel(["P",xa,xb],["C",y,xa])]]),
#[["I",xa],["C",y,xb],["I",xa],["C",y,xb^-1]],
	applyrels([["I",xa],["C",y,xb],["I",xa],["C",y,xb^-1]],[[0,dphirel(["I",xa],["C",y,xb])]]),
#[["I",xa],["C",y,xa],["I",xa],["C",y,xa]],
	applyrels([["I",xa],["C",y,xa],["I",xa],["C",y,xa]],[[0,dphirel(["I",xa],["C",y,xa])]]),
#[["P",xa,xb],["M",xc,y],["P",xa,xb],["M",xc,y^-1]],
	applyrels([["P",xa,xb],["M",xc,y],["P",xa,xb],["M",xc,y^-1]],[[0,dpsirel(["P",xa,xb],["M",xc,y])]]),
#[["P",xa,xb],["M",xa,y],["P",xa,xb],["M",xb,y^-1]],
	applyrels([["P",xa,xb],["M",xa,y],["P",xa,xb],["M",xb,y^-1]],[[0,dpsirel(["P",xa,xb],["M",xa,y])]]),
#[["I",xa],["M",xb,y],["I",xa],["M",xb,y^-1]],
	applyrels([["I",xa],["M",xb,y],["I",xa],["M",xb,y^-1]],[[0,dpsirel(["I",xa],["M",xb,y])]]),
#[["I",xa],["M",xa,y],["I",xa],["M",xa,y],["C",xa,y^-1]],
	applyrels([["I",xa],["M",xa,y],["I",xa],["M",xa,y],["C",xa,y^-1]],[[0,dpsirel(["I",xa],["M",xa,y])]]),
#[["P",xa,xb],["C",xc,y],["M",xc,y^-1],["P",xa,xb],["M",xc,y],["C",xc,y^-1]],
	applyrels([["P",xa,xb],["C",xc,y],["M",xc,y^-1],["P",xa,xb],["M",xc,y],["C",xc,y^-1]],[[3,dpsirel(["P",xa,xb],["M",xc,y])],[0,dphirel(["P",xa,xb],["C",xc,y])]]),
#[["P",xa,xb],["C",xa,y],["M",xa,y^-1],["P",xa,xb],["M",xb,y],["C",xb,y^-1]],
	applyrels([["P",xa,xb],["C",xa,y],["M",xa,y^-1],["P",xa,xb],["M",xb,y],["C",xb,y^-1]],[[5,dpsirel(["P",xa,xb],["M",xa,y^-1])],[0,dphirel(["P",xa,xb],["C",xa,y])]]),
#[["I",xa],["C",xb,y],["M",xb,y^-1],["I",xa],["M",xb,y],["C",xb,y^-1]],
	applyrels([["I",xa],["C",xb,y],["M",xb,y^-1],["I",xa],["M",xb,y],["C",xb,y^-1]],[[3,dpsirel(["I",xa],["M",xb,y])],[0,dphirel(["I",xa],["C",xb,y])]]),
#[["I",xa],["C",xa,y],["M",xa,y^-1],["I",xa],["M",xa,y^-1]],
	applyrels([["I",xa],["C",xa,y],["M",xa,y^-1],["I",xa],["M",xa,y^-1]],[[1,iw(dpsirel(["I",xa],["M",xa,y]))]]),

#Q4 Relations
#[["M",xa,xb^-1],["M",xb,y],["M",xa,xb],["M",xb,y^-1],["M",xa,y^-1]],
	applyrels([["M",xa,xb^-1],["M",xb,y],["M",xa,xb],["M",xb,y^-1],["M",xa,y^-1]],[[0,dpsirel(["M",xa,xb^-1],["M",xb,y])],[0,znrel(xa,xb)]]),
#[["M",xa,xb],["C",xb,y],["M",xb,y^-1],["M",xa,xb^-1],["M",xb,y],["C",xb,y^-1],["M",xa,y^-1]],
	applyrels([["M",xa,xb],["C",xb,y],["M",xb,y^-1],["M",xa,xb^-1],["M",xb,y],["C",xb,y^-1],["M",xa,y^-1]],[[0,dphirel(["M",xa,xb],["C",xb,y])],[2,dpsirel(["M",xa,xb],["M",xb,y^-1])],[2,znrel(xb,xa)],[1,dphirel(["M",xa,y],["C",xb,y^-1])]]),
#[["M",xa^-1,xb^-1],["M",xb,y],["M",xa^-1,xb],["M",xb,y^-1],["M",xa,y],["C",xa,y^-1]],
	applyrels([["M",xa^-1,xb^-1],["M",xb,y],["M",xa^-1,xb],["M",xb,y^-1],["M",xa,y],["C",xa,y^-1]],[[0,dpsirel(["M",xa^-1,xb^-1],["M",xb,y])],[4,znrel(xb,xa)]]),
#[["M",xa^-1,xb],["C",xb,y],["M",xb,y^-1],["M",xa^-1,xb^-1],["M",xb,y],["C",xb,y^-1],["M",xa,y],["C",xa,y^-1]],
	applyrels([["M",xa^-1,xb],["C",xb,y],["M",xb,y^-1],["M",xa^-1,xb^-1],["M",xb,y],["C",xb,y^-1],["M",xa,y],["C",xa,y^-1]],[[0,dphirel(["M",xa^-1,xb],["C",xb,y])],[2,dpsirel(["M",xa^-1,xb],["M",xb,y^-1])],[3,krel(6,[xa^-1,y^-1,xb^-1])],[4,znrel(xa,xb)],[2,dphirel(["M",xa,y^-1],["C",xb,y^-1])],[0,krel(1,[xa,xb])]]),

#Q5 Relations
#[["C",y,xa^-1],["C",xa,y],["M",xa,y^-1],["C",y,xa],["M",xa,y]],
	applyrels([["C",y,xa^-1],["C",xa,y],["M",xa,y^-1],["C",y,xa],["M",xa,y]],[[2,dphirel(["M",xa,y^-1],["C",y,xa])]]),
#[["C",y,xa],["M",xa,y],["C",y,xa^-1],["C",xa,y],["M",xa,y^-1]],
	applyrels([["C",y,xa],["M",xa,y],["C",y,xa^-1],["C",xa,y],["M",xa,y^-1]],[[4,dphirel(["M",xa,y^-1],["C",y,xa])]])
];

BirmanIAchecklist:=[
["exkrellist",exkrellist],
["phiconjugationlist",phiconjugationlist],
["phiAinverselist",phiAinverselist],
["phiZinverselist",phiZinverselist],
["phiN3list",phiN3list],
["phiN4list",phiN4list],
["phiN5list",phiN5list],
["phiznlist",phiznlist],
["lambda2ndinverselist",lambda2ndinverselist],
["lambda2ndrellist",lambda2ndrellist],
["tb3list",tb3list],
["lambda1stinverselist",lambda2ndinverselist],
["lambdaN1list",lambdaN1list],
["lambdaN2list",lambdaN2list],
["lambdaN3list",lambdaN3list],
["lambdaN4list",lambdaN4list],
["lambdaN5list",lambdaN5list],
["verifyGammarellist",verifyGammarellist],
["JWfromDeltalist",JWfromDeltalist]
];
