# GAP code for "On the second homology group of the Torelli subgroup of Aut(F_n)".
# Revised August 2015.

# General things for working in the free group on IA_n and Aut(F_n) generators
##############################################
fg := FreeGroup( "xa", "xb", "xc", "xd", "xe", "xf", "xg", "y");  

# We use this "fg" as the free group F_n.  
# Generators for subgroups of Aut(F_n) take parameters in these generators.

AssignGeneratorVariables(fg);				#This creates global variables "xa", ... , "xf", "y" that represent the corresponding generators of fg.
invertmove := function(mov)				#takes in a generator from IA_n or Aut(F_n), represented as a list, and returns its inverse
	if not IsList(mov) then return; fi;		#quit if not given a list as input
	if mov[1]="M" or mov[1]="C" then		
		return [mov[1],mov[2],Inverse(mov[3])];	#invert "M" or "C" move by inverting last parameter
	elif mov[1]="Mc" then
		return [mov[1],mov[2],mov[4],mov[3]];	#invert commutator transvection by swapping order of last two parameters, this hard-codes R0
	elif mov[1]="I" or mov[1]="P" then
		return mov;				#inversion moves and swaps are their own inverses
	fi;
end;
iw := function(list)					#takes a word and returns its inverse
	local out;
	out := Reversed(list);
	Apply(out, invertmove);
	return out;
end;

freereducemovelist :=function(movelist)			#Takes in a word and reduces inverse pairs that word
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

cycredw := function(word)
	local out;

	out:= StructuralCopy(word);
	while Length(out)>1 and out[1]=invertmove(out[Length(out)]) do
		Remove(out,Length(out));
		Remove(out,1);
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
wellformedkgen := function(move)			#returns true if given a list correctly rerpesenting a generator from Torelli deletion kernel 
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

basisorder := function(belt)			#This is used only by ispositive. It puts an ordering on the basis elements.
	if genof(belt)=y then return 1;
	elif genof(belt)=xa then return 2;
	elif genof(belt)=xb then return 3;
	elif genof(belt)=xc then return 4;
	elif genof(belt)=xd then return 5;
	elif genof(belt)=xe then return 6;
	elif genof(belt)=xf then return 7;
	elif genof(belt)=xg then return 8;
	fi;
	return 999;
end;

ispositive := function(mov)	#Tests whether generators are positive.
	if mov[1]="M" or mov[1]="C" then		#"M" and "C" generators are positive if their last parameter is
		if ExtRepOfObj(mov[3])[2]<0 then
			return false;
		else 
			return true;
		fi;
	elif mov[1]="Mc" then				#"Mc" generators are positive if the third parameter is ordered earlier than fourth parameter in ordering
		if basisorder(mov[3])<basisorder(mov[4]) then
			return true;
		else
			return false;
		fi;
	else
		return true;				#"P" and "I" generators are always positive
	fi;
end;


applyrels := function(startword, rels)			# This inserts a sequence of words (usually relations) into a given word at given posititions, reducing in between inserting the words
	if Length(rels)=0 then 
		return startword;
	elif rels[1][1]=0 then
		return applyrels( pw(rels[1][2],startword) , rels{[2..Length(rels)]});
	else
		return applyrels( pw(startword{[1..rels[1][1]]},rels[1][2],startword{[(rels[1][1]+1)..Length(startword)]}) , rels{[2..Length(rels)]});
	fi;
end;

cyw := function(sh,word)				# This cycles the input word by the input number, to the left if positive and to the right if negative.
	if Length(word)=0 or sh=0 then return word;
	elif sh>0 then
		return pw(word{[sh+1..Length(word)]},word{[1..sh]});
	else
		return pw(word{[Length(word)+sh+1..Length(word)]},word{[1..Length(word)+sh]});
	fi;
end;



# Functions for interpreting generators as automorphisms and evaluating them
############################################################################

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
wordtolistoffunctions:=function(listoflist) 	#takes a word, returns the corresponding list of functions on fg
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
basischeckfns := function(pair)	#takes a pair of functions on fg and returns true if the have the same action on generators, false otherwise
	local left, right;
	left := basischeck(composemoves(pair[1]));
	right := basischeck(composemoves(pair[2]));
	if left=right then
		return true;
	else
		return false;
	fi;	
end;
basischeckwords := function(pair)	#takes a pair of words and returns true if they represent the same automorphism of fg, false otherwise
	return basischeckfns([wordtolistoffunctions(pair[1]),wordtolistoffunctions(pair[2])]);
end;

# Functions that generate lists of relations and functions on strings of words
##############################################################################

# Basic and extra relations for IA_n.

# iarel takes in a relation number (1--9) and a list of parameters, e.g. iarel(1, [xa,xb,xc,xd]).
# The number of parameters and the coincidences allowed in the parameters depend on the relation, but match the table in the paper.  
# It returns the specified relation as a word. It returns [] if given bad data.

iarel := function(relno, params)	
	local m1, m2, m3, m4;
	if relno=1 then	 	#iarel(1,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[2]]; 
		m2 := ["C",genof(params[3]),params[4]];
		if m1[2]<>m2[2] and m1[2]<>genof(m2[3]) and genof(m1[3])<>m2[2] 
			then return [m1,m2,invertmove(m1),invertmove(m2)]; 
		else return []; 
		fi;
	elif relno=2 then	#iarel(2,...) needs 6 parameters.		
		m1:=["Mc",params[1],params[2],params[3]];
		m2:=["Mc",params[4],params[5],params[6]];
		if m1[2]<>m2[3] and m1[2]<>m2[3]^-1 and m1[2]<>m2[4] and m1[2]<>m2[4]^-1 and m2[2]<>m1[3] and m2[2]<>m1[3]^-1 and m2[2]<>m1[4] and m2[2]<>m1[4]^-1 and m1[2]<>m2[2]
			then return [m1, m2, invertmove(m1),invertmove(m2)];
		else return [];
		fi;
	elif relno=3 then	#iarel(3,...) needs 5 parameters.
		m1:=["C", genof(params[4]),params[5]];
		m2:=["Mc",params[1],params[2],params[3]];
		if m1[2]<>m2[3] and m1[2]<>m2[3]^-1 and m1[2]<>m2[4] and m1[2]<>m2[4]^-1 and m1[2]<>m2[2] and m1[2]<>m2[2]^-1 and m1[3]<>m2[2] and m1[3]<>m2[2]^-1
			then return [m1, m2, invertmove(m1),invertmove(m2)];
		else return [];
		fi;
	elif relno=4 then	#iarel(4,...) needs 3 parameters.
		m1:=["C",genof(params[1]),params[2]];
		m2:=["C",genof(params[3]),params[1]];
		m3:=["C",genof(params[3]),params[2]];
		if m1[2]<>m2[2] and m1[2]<>genof(m1[3]) and m2[2]<>genof(m1[3])
			then return [m1,m2,invertmove(m1),invertmove(m3),invertmove(m2),m3];
		else return [];
		fi;
	elif relno=5 then	#iarel(5,...) needs 3 parameters.
		m1:=["C",genof(params[1]),params[2]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) then
			return [m1,["Mc",params[1],params[2],params[3]],invertmove(m1),["Mc",params[1],params[2]^-1,params[3]]];
		else return [];
		fi;
	elif relno=6 then	#iarel(6,...) needs 3 parameters.
		m1:=["C",genof(params[1]),params[2]];
		m2:=["C",genof(params[1]),params[3]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) then
			return [["Mc",params[1],params[2],params[3]],["Mc",params[1]^-1,params[2],params[3]],invertmove(m1),invertmove(m2),m1,m2];
		else return [];
		fi;
	elif relno=7 then	#iarel(7,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[3]];
		m2:=["C",genof(params[1]),params[4]];
		m3:=["C",genof(params[1]),params[2]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[2])<>genof(params[4]) and genof(params[3])<>genof(params[4])
			then return [ invertmove(m1),invertmove(m2),m1, m2, invertmove(m3), [ "Mc", params[2], params[3], params[4] ], m3, [ "Mc", params[2], params[4], params[3] ] ];
		else return [];
		fi;
	elif relno=8 then	#iarel(8,...) needs 5 parameters.
		m1:=["Mc",params[1],params[2],params[3]];
		m2:=["Mc",params[4],params[1],params[5]];
		m3:=["C",genof(params[4]),params[5]];
		if 
		genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) 
		and genof(params[1])<>genof(params[4]) and genof(params[1])<>genof(params[5]) and genof(params[4])<>genof(params[5])
		and genof(params[4])<>genof(params[2]) and genof(params[4])<>genof(params[3])  
			then return [ m1, m2, invertmove(m1),   [ "Mc", params[4], params[3], params[2] ], invertmove(m2), invertmove(m3),  [ "Mc", params[4], params[2], params[3] ], m3 ];
		else return [];
		fi;
	elif relno=9 then	#iarel(9,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[2]];
		m2:=["C",genof(params[3]),params[4]];
		m3:=["Mc", params[3],params[4],params[1]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[3])<>genof(params[4]) then 
			if params[2]<>params[4] then
return [ m1,m3, invertmove(m1),invertmove(m2), [ "Mc", params[3], params[1], params[2] ], m2,invertmove(m3), [ "Mc", params[3], params[2], params[1] ] ] ;
			else
return [ m1,m3, invertmove(m1),invertmove(m2), [ "Mc", params[3], params[1], params[2] ], m2] ;
			fi;
		else return [];
		fi;
	else return [];
	fi;
end;

# exiarel functions like iarel.  The best guide to this function is to try it on test input.

exiarel := function(relno, params)	
	local m1, m2, m3, m4, m5, m6, m7, m8, m9;
	if relno=1 then 	#exiarel(1,...) needs 3 parameters.
		m1:=["C",genof(params[1]),params[2]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) then
			return [invertmove(m1),["Mc",params[3],params[1],params[2]],m1,["Mc",params[3],params[1],params[2]^-1]];
		else return [];
		fi;
	elif relno=2 then	#exiarel(2,...) needs 5 parameters.
		m1:=["Mc",params[1],params[2],params[3]];
		m2:=["C",genof(params[4]),params[1]];
		m3:=["C",genof(params[4]),params[5]];
		m4:=["Mc",params[4],params[1]^-1,params[5]];
		m5:=["Mc",params[4],params[2],params[3]];
		if 
		genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) 
		and genof(params[1])<>genof(params[4]) and genof(params[1])<>genof(params[5]) and genof(params[4])<>genof(params[5])
		and genof(params[4])<>genof(params[2]) and genof(params[4])<>genof(params[3])  
			then return [m1,m4,invertmove(m1),m2,m5,invertmove(m3),invertmove(m5),m3,invertmove(m2),invertmove(m4)];
		else return [];
		fi;
	elif relno=3 then	#exiarel(3,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[4]];
		m2:=["C",genof(params[2]),params[4]];
		m3:=["C",genof(params[3]),params[4]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[2])<>genof(params[4]) and genof(params[3])<>genof(params[4])
			then return [[ "Mc", params[1], params[2], params[3] ], m1,m2,m3,[ "Mc", params[1], params[3], params[2] ],invertmove(m3),invertmove(m2),invertmove(m1)];
		else return [];
		fi;
	elif relno=4 then	#exiarel(4,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[2]];
		m2:=["C",genof(params[1]),params[3]];
		m3:=["C",genof(params[1]),params[4]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[2])<>genof(params[4]) and genof(params[3])<>genof(params[4])
			then return [["Mc",params[1],params[2],params[3]],invertmove(m1),["Mc",params[1],params[4],params[3]],m1,["Mc",params[1],params[4],params[2]],invertmove(m3),["Mc",params[1],params[3],params[2]],m3,["Mc",params[1],params[3],params[4]],invertmove(m2),["Mc",params[1],params[2],params[4]],m2];
		else return [];
		fi;
	elif relno=5 then	#exiarel(5,...) needs 6 parameters.
		m1:=["C",genof(params[1]),params[4]];
		m2:=["C",genof(params[2]),params[4]];
		m3:=["C",genof(params[3]),params[4]];
		m4:=["C",genof(params[5]),params[6]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[2])<>genof(params[4]) and genof(params[3])<>genof(params[4]) and genof(params[4])<>genof(params[5])  then
		return [m1,m2,m3,m4,invertmove(m3),invertmove(m2),invertmove(m1),invertmove(m4)];
		else return [];
		fi;
	elif relno=6 then	#exiarel(6,...) needs 3 parameters.
		m1:=["C",genof(params[2]),params[1]];
		m2:=["C",genof(params[3]),params[1]];
		m3:=["C",genof(params[3]),params[2]];
		m4:=["C",genof(params[2]),params[3]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) then
			return [m1, m2, [ "Mc", params[1], params[2], params[3] ], invertmove(m2), invertmove(m1), [ "Mc", params[1]^-1, params[2], params[3] ], m3, m4, invertmove(m3), invertmove(m4)];
		else return [];
		fi;
	elif relno=7 then	#exiarel(7,...) needs 3 parameters.
		m1:=["C",genof(params[1]),params[2]];
		m2:=["C",genof(params[1]),params[3]];
		m3:=["C",genof(params[2]),params[1]];
		m4:=["C",genof(params[2]),params[3]];
		m5:=["C",genof(params[3]),params[1]];
		m6:=["C",genof(params[3]),params[2]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[2])<>genof(params[3]) then
			return [invertmove(m5),invertmove(m3),m2,m4,m1,m6,invertmove(m4),invertmove(m2),invertmove(m6),invertmove(m1), [ "Mc", params[1], params[2], params[3] ],m3,m5,[ "Mc", params[1],params[3],params[2]]];
		
		else return [];
		fi;
	elif relno=8 then	#exiarel(8,...) needs 4 parameters.
		m1:=["C",genof(params[1]),params[3]];
		m2:=["C",genof(params[2]),params[3]];
		m3:=["C",genof(params[4]),params[3]];
		m4:=["C",genof(params[1]),params[2]];
		m5:=["C",genof(params[3]),params[2]];
		m6:=["C",genof(params[4]),params[2]];
		m7:=["C",genof(params[2]),params[1]];
		m8:=["C",genof(params[3]),params[1]];
		m9:=["C",genof(params[4]),params[1]];
		if genof(params[1])<>genof(params[2]) and genof(params[1])<>genof(params[3]) and genof(params[1])<>genof(params[4]) and genof(params[2])<>genof(params[3]) and genof(params[2])<>genof(params[4]) and genof(params[3])<>genof(params[4])
			then return [ m1, m2, m3, m4, m5, m6, invertmove(m3), invertmove(m2), invertmove(m1), invertmove(m6), invertmove(m5), invertmove(m4), [ "Mc", params[1], params[2], params[3] ], m7, m8, m9, [ "Mc", params[1], params[3], params[2] ], invertmove(m9), invertmove(m8), invertmove(m7) ];
		else return [];
		fi;
	else return [];
	fi;
end;

# Basic relations for the Torelli deletion kernel
# krel returns relations for the deletion kernel, as explained in Day--Putman "A Birman exact sequence for the Torelli subgroup of Aut(F_n)"
# this works similarly to iarel
krel := function(relno, params)	
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


# Functions defining theta, substitution rule function for the L-presentation for IA_n

thetaongens := function(by,on)	# defines theta on generators and returns a word
	if not ispositive(on) then
		return iw(thetaongens(by,invertmove(on)));
	fi;
	if by[1]="M" then
		if on[1]="C" then
			if genof(on[2])=genof(by[2]) then
				if genof(on[3])=genof(by[3]) then 
					return [on];
				else
					return [on,["Mc",by[2],by[3]^-1,on[3]]];
				fi;
			elif genof(on[2])=genof(by[3]) then
				if genof(on[3])=genof(by[2]) then
					if on[3]=by[2] then
						return [["C",genof(by[2]),by[3]],on];
					else
						return [on,["C",genof(by[2]),by[3]^-1]];
					fi;
				else
					return [on,["Mc",by[2],by[3]^-1,on[3]^-1]];
				fi;
			elif genof(on[3])=genof(by[2]) then
				if on[3]=by[2] then
					return [on,["C",genof(on[2]),by[3]]];
				else
					return [["C",genof(on[2]),by[3]^-1],on];
				fi;
			else 
				return [on];
			fi;
		elif on[1]="Mc" then
			if on[2]=by[2] then
				return [["C",genof(by[2]),by[3]],on,["C",genof(by[2]),by[3]^-1]];
			elif on[2]=by[2]^-1 then
				return [on];
			elif on[2]=by[3] and on[3]=by[2] then
				return [["C",genof(by[2]),on[4]],["Mc",by[2],by[3]^-1,on[4]],["C",genof(by[3]),on[4]^-1],["Mc",by[3]^-1,by[2],on[4]^-1]];
			elif on[2]=by[3] and on[4]=by[2] then
				return iw([["C",genof(by[2]),on[3]],["Mc",by[2],by[3]^-1,on[3]],["C",genof(by[3]),on[3]^-1],["Mc",by[3]^-1,by[2],on[3]^-1]]);
			elif on[2]=by[3] and on[3]=by[2]^-1 then
				return [["C",genof(on[4]),by[3]^-1],["C",genof(on[4]),by[2]^-1],["Mc",by[3]^-1,on[4]^-1,by[2]],["C",genof(by[3]),on[4]],["Mc",by[2],on[4],by[3]^-1],["C",genof(by[2]),on[4]^-1],["C",genof(on[4]),by[2]],["C",genof(on[4]),by[3]]];
			elif on[2]=by[3] and on[4]=by[2]^-1 then
				return iw([["C",genof(on[3]),by[3]^-1],["C",genof(on[3]),by[2]^-1],["Mc",by[3]^-1,on[3]^-1,by[2]],["C",genof(by[3]),on[3]],["Mc",by[2],on[3],by[3]^-1],["C",genof(by[2]),on[3]^-1],["C",genof(on[3]),by[2]],["C",genof(on[3]),by[3]]]);
			elif on[2]=by[3]^-1 and on[3]=by[2] then
				return [["C",genof(by[2]),on[4]^-1],["C",genof(on[4]),by[2]],["Mc",by[3]^-1,on[4],by[2]^-1],["C",genof(on[4]),by[3]],["Mc",by[2],on[4],by[3]^-1],["C",genof(by[3]),on[4]],["C",genof(on[4]),by[3]^-1],["C",genof(on[4]),by[2]^-1]];
			elif on[2]=by[3]^-1 and on[4]=by[2] then
				return iw([["C",genof(by[2]),on[3]^-1],["C",genof(on[3]),by[2]],["Mc",by[3]^-1,on[3],by[2]^-1],["C",genof(on[3]),by[3]],["Mc",by[2],on[3],by[3]^-1],["C",genof(by[3]),on[3]],["C",genof(on[3]),by[3]^-1],["C",genof(on[3]),by[2]^-1]]);
			elif on[2]=by[3]^-1 and on[3]=by[2]^-1 then
				return [["C",genof(by[3]),on[4]^-1],["Mc",by[2],by[3]^-1,on[4]],["C",genof(on[4]),by[3]^-1],["Mc",by[3]^-1,by[2]^-1,on[4]],["C",genof(on[4]),by[2]^-1],["C",genof(by[2]),on[4]],["C",genof(on[4]),by[2]],["C",genof(on[4]),by[3]]];
			elif on[2]=by[3]^-1 and on[4]=by[2]^-1 then
				return iw([["C",genof(by[3]),on[3]^-1],["Mc",by[2],by[3]^-1,on[3]],["C",genof(on[3]),by[3]^-1],["Mc",by[3]^-1,by[2]^-1,on[3]],["C",genof(on[3]),by[2]^-1],["C",genof(by[2]),on[3]],["C",genof(on[3]),by[2]],["C",genof(on[3]),by[3]]]);
			elif on[2]=by[3] then
				return [["C",genof(by[2]),by[3]],["Mc",by[2]^-1,on[3],on[4]],["Mc",by[3],on[3],on[4]],["C",genof(by[2]),by[3]^-1]];
			elif on[2]=by[3]^-1 then
				return [["Mc",by[2],on[3],on[4]],["Mc",by[3]^-1,on[3],on[4]]];
			elif on[3]=by[2] and on[4]=by[3] then
				return [["C",genof(by[2]),by[3]],on,["C",genof(by[2]),by[3]^-1]];
			elif on[4]=by[2] and on[3]=by[3] then
				return [["C",genof(by[2]),by[3]],on,["C",genof(by[2]),by[3]^-1]];
			elif on[3]=by[2] and on[4]=by[3]^-1 then
				return [["Mc",on[2],by[3],by[2]]];
			elif on[4]=by[2] and on[3]=by[3]^-1 then
				return [["Mc",on[2],by[2],by[3]]];
			elif on[3]=by[2]^-1 and genof(on[4])=genof(by[3]) then
				return [on];
			elif on[4]=by[2]^-1 and genof(on[3])=genof(by[3]) then
				return [on];
			elif on[3]=by[2] then
				return [["Mc",on[2],by[3],on[4]],["C",genof(on[2]),by[3]^-1],on,["C",genof(on[2]),by[3]]];
			elif on[4]=by[2] then
				return iw([["Mc",on[2],by[3],on[3]],["C",genof(on[2]),by[3]^-1],["Mc",on[2],on[4],on[3]],["C",genof(on[2]),by[3]]]);
			elif on[3]=by[2]^-1 then
				return [on,["C",genof(on[2]),by[2]],["Mc",on[2],by[3]^-1,on[4]],["C",genof(on[2]),by[2]^-1]];
			elif on[4]=by[2]^-1 then
				return iw([["Mc",on[2],on[4],on[3]],["C",genof(on[2]),by[2]],["Mc",on[2],by[3]^-1,on[3]],["C",genof(on[2]),by[2]^-1]]);
			else
				return [on];
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
thetagenword := function(by,list) # defines theta acting by a single generator, but acting on a word, returns a word
	local out, on;
	out:=[];
	for on in list do
		Append(out,thetaongens(by,on));
	od;
	return freereducemovelist(out);
end;
theta := function(bylist,onlist)	#defines theta, takes in two words and returns a word
	local bymove, bybackwards, out;
	if bylist=[] then return onlist; fi;
	out:=onlist;
	bybackwards:=Reversed(bylist);
	for bymove in bybackwards do
		out := thetagenword(bymove, out);
	od;
	return out;
end;

# Functions defining phi, the substitution rule function for the L-presentation for the Torelli deletion kernel
# This is explained in Day--Putman "A Birman exact sequence for the Torelli subgroup of Aut(F_n)"

phiongens := function(by,on)	#action function phi in the special case that both inputs are single generators.   returns a word.
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
phigenword := function(by,list) #phi in special case input is a (generator, word) pair. It returns a word.
	local out, on;
	out:=[];
	for on in list do
		Append(out,phiongens(by,on));
	od;
	return freereducemovelist(out);
end;
phi := function(bylist,onlist)	#phi in general case, input is a pair of words. It returns a word.
	local bymove, bybackwards, out;
	if bylist=[] then return onlist; fi;
	out:=onlist;
	bybackwards:=Reversed(bylist);
	for bymove in bybackwards do
		out := phigenword(bymove, out);
	od;
	return out;
end;



# Here we start generating lists that verify assertions in the paper
####################################################################

# Verifying that the basic relations are true in IA_n

verifyiarel:=[
basischeckwords([iarel(1,[xa,xb,xc,xd]),[]]),
basischeckwords([iarel(1,[xa,xb,xc,xb]),[]]),
basischeckwords([iarel(1,[xa,xb,xc,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xe,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xe,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xe,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb^-1,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xe,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xe,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc^-1,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb^-1,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xb,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc^-1,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xd,xc,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xe,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xe,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xe,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb^-1,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xe,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xe,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc^-1,xf]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb^-1,xc]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xb,xc^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc,xb^-1]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc^-1,xb]),[]]),
basischeckwords([iarel(2,[xa,xb,xc,xa^-1,xc,xb^-1]),[]]),
basischeckwords([iarel(3,[xa,xb,xc,xd,xe]),[]]),
basischeckwords([iarel(3,[xa,xe,xc,xd,xe]),[]]),
basischeckwords([iarel(3,[xa,xe^-1,xc,xd,xe]),[]]),
basischeckwords([iarel(3,[xa,xb,xe,xd,xe]),[]]),
basischeckwords([iarel(3,[xa,xb,xe^-1,xd,xe]),[]]),
basischeckwords([iarel(4,[xa,xb,xc]),[]]),
basischeckwords([iarel(5,[xa,xb,xc]),[]]),
basischeckwords([iarel(6,[xa,xb,xc]),[]]),
basischeckwords([iarel(7,[xa,xb,xc,xd]),[]]),
basischeckwords([iarel(8,[xa,xb,xc,xd,xe]),[]]),
basischeckwords([iarel(8,[xa,xe,xc,xd,xe]),[]]),
basischeckwords([iarel(8,[xa,xe^-1,xc,xd,xe]),[]]),
basischeckwords([iarel(8,[xa,xb,xe,xd,xe]),[]]),
basischeckwords([iarel(8,[xa,xb,xe^-1,xd,xe]),[]]),
basischeckwords([iarel(9,[xa,xb,xc,xd]),[]]),
basischeckwords([iarel(9,[xa,xd,xc,xd]),[]]),
basischeckwords([iarel(9,[xa,xd^-1,xc,xd]),[]]),
];


# Verifying that theta acts as expected in Aut(F_n)
thetatest:=function(by,on)
	return basischeckwords([cw([by],[on]),theta([by],[on])]);
end;
thetavsconjaut:=
[
thetatest(["I",xa],["C",xc,xd]),
thetatest(["I",xa],["C",xa,xd]),
thetatest(["I",xa],["C",xc,xa]),
thetatest(["I",xa],["C",xc,xa^-1]),
thetatest(["I",xa],["Mc",xc,xd,xe]),
thetatest(["I",xa],["Mc",xa,xd,xe]),
thetatest(["I",xa],["Mc",xa^-1,xd,xe]),
thetatest(["I",xa],["Mc",xc,xa,xe]),
thetatest(["I",xa],["Mc",xc,xa^-1,xe]),
thetatest(["I",xa],["Mc",xc,xd,xa]),
thetatest(["I",xa],["Mc",xc,xd,xa^-1]),

thetatest(["P",xa,xb],["C",xc,xd]),
thetatest(["P",xa,xb],["C",xa,xd]),
thetatest(["P",xa,xb],["C",xc,xa]),
thetatest(["P",xa,xb],["C",xc,xa^-1]),
thetatest(["P",xa,xb],["C",xb,xd]),
thetatest(["P",xa,xb],["C",xc,xb]),
thetatest(["P",xa,xb],["C",xc,xb^-1]),
thetatest(["P",xa,xb],["C",xa,xb]),
thetatest(["P",xa,xb],["C",xa,xb^-1]),
thetatest(["P",xa,xb],["C",xb,xa]),
thetatest(["P",xa,xb],["C",xb,xa^-1]),
thetatest(["P",xa,xb],["Mc",xc,xd,xe]),
thetatest(["P",xa,xb],["Mc",xa,xd,xe]),
thetatest(["P",xa,xb],["Mc",xa^-1,xd,xe]),
thetatest(["P",xa,xb],["Mc",xc,xa,xe]),
thetatest(["P",xa,xb],["Mc",xc,xa^-1,xe]),
thetatest(["P",xa,xb],["Mc",xc,xd,xa]),
thetatest(["P",xa,xb],["Mc",xc,xd,xa^-1]),
thetatest(["P",xa,xb],["Mc",xb,xd,xe]),
thetatest(["P",xa,xb],["Mc",xb^-1,xd,xe]),
thetatest(["P",xa,xb],["Mc",xc,xb,xe]),
thetatest(["P",xa,xb],["Mc",xc,xb^-1,xe]),
thetatest(["P",xa,xb],["Mc",xc,xd,xb]),
thetatest(["P",xa,xb],["Mc",xc,xd,xb^-1]),
thetatest(["P",xa,xb],["Mc",xa,xb,xe]),
thetatest(["P",xa,xb],["Mc",xa,xb^-1,xe]),
thetatest(["P",xa,xb],["Mc",xa^-1,xb,xe]),
thetatest(["P",xa,xb],["Mc",xa^-1,xb^-1,xe]),
thetatest(["P",xa,xb],["Mc",xa,xd,xb]),
thetatest(["P",xa,xb],["Mc",xa^-1,xd,xb]),
thetatest(["P",xa,xb],["Mc",xa,xd,xb^-1]),
thetatest(["P",xa,xb],["Mc",xa^-1,xd,xb^-1]),
thetatest(["P",xa,xb],["Mc",xb,xa,xe]),
thetatest(["P",xa,xb],["Mc",xb^-1,xa,xe]),
thetatest(["P",xa,xb],["Mc",xb,xa^-1,xe]),
thetatest(["P",xa,xb],["Mc",xb^-1,xa^-1,xe]),
thetatest(["P",xa,xb],["Mc",xb,xd,xa]),
thetatest(["P",xa,xb],["Mc",xb^-1,xd,xa]),
thetatest(["P",xa,xb],["Mc",xb,xd,xa^-1]),
thetatest(["P",xa,xb],["Mc",xb^-1,xd,xa^-1]),
thetatest(["P",xa,xb],["Mc",xc,xa,xb]),
thetatest(["P",xa,xb],["Mc",xc,xa^-1,xb]),
thetatest(["P",xa,xb],["Mc",xc,xa,xb^-1]),
thetatest(["P",xa,xb],["Mc",xc,xa^-1,xb^-1]),
thetatest(["P",xa,xb],["Mc",xc,xb,xa]),
thetatest(["P",xa,xb],["Mc",xc,xb^-1,xa]),
thetatest(["P",xa,xb],["Mc",xc,xb,xa^-1]),
thetatest(["P",xa,xb],["Mc",xc,xb^-1,xa^-1]),

thetatest(["M",xa,xb],["C",xc,xd]),
thetatest(["M",xa,xb],["C",xa,xd]),
thetatest(["M",xa,xb],["C",xc,xa]),
thetatest(["M",xa,xb],["C",xc,xa^-1]),
thetatest(["M",xa,xb],["C",xb,xd]),
thetatest(["M",xa,xb],["C",xc,xb]),
thetatest(["M",xa,xb],["C",xc,xb^-1]),
thetatest(["M",xa,xb],["C",xa,xb]),
thetatest(["M",xa,xb],["C",xa,xb^-1]),
thetatest(["M",xa,xb],["C",xb,xa]),
thetatest(["M",xa,xb],["C",xb,xa^-1]),
thetatest(["M",xa,xb],["Mc",xc,xd,xe]),
thetatest(["M",xa,xb],["Mc",xa,xd,xe]),
thetatest(["M",xa,xb],["Mc",xa^-1,xd,xe]),
thetatest(["M",xa,xb],["Mc",xc,xa,xe]),
thetatest(["M",xa,xb],["Mc",xc,xa^-1,xe]),
thetatest(["M",xa,xb],["Mc",xc,xd,xa]),
thetatest(["M",xa,xb],["Mc",xc,xd,xa^-1]),
thetatest(["M",xa,xb],["Mc",xb,xd,xe]),
thetatest(["M",xa,xb],["Mc",xb^-1,xd,xe]),
thetatest(["M",xa,xb],["Mc",xc,xb,xe]),
thetatest(["M",xa,xb],["Mc",xc,xb^-1,xe]),
thetatest(["M",xa,xb],["Mc",xc,xd,xb]),
thetatest(["M",xa,xb],["Mc",xc,xd,xb^-1]),
thetatest(["M",xa,xb],["Mc",xa,xb,xe]),
thetatest(["M",xa,xb],["Mc",xa,xb^-1,xe]),
thetatest(["M",xa,xb],["Mc",xa^-1,xb,xe]),
thetatest(["M",xa,xb],["Mc",xa^-1,xb^-1,xe]),
thetatest(["M",xa,xb],["Mc",xa,xd,xb]),
thetatest(["M",xa,xb],["Mc",xa^-1,xd,xb]),
thetatest(["M",xa,xb],["Mc",xa,xd,xb^-1]),
thetatest(["M",xa,xb],["Mc",xa^-1,xd,xb^-1]),
thetatest(["M",xa,xb],["Mc",xb,xa,xe]),
thetatest(["M",xa,xb],["Mc",xb^-1,xa,xe]),
thetatest(["M",xa,xb],["Mc",xb,xa^-1,xe]),
thetatest(["M",xa,xb],["Mc",xb^-1,xa^-1,xe]),
thetatest(["M",xa,xb],["Mc",xb,xd,xa]),
thetatest(["M",xa,xb],["Mc",xb^-1,xd,xa]),
thetatest(["M",xa,xb],["Mc",xb,xd,xa^-1]),
thetatest(["M",xa,xb],["Mc",xb^-1,xd,xa^-1]),
thetatest(["M",xa,xb],["Mc",xc,xa,xb]),
thetatest(["M",xa,xb],["Mc",xc,xa^-1,xb]),
thetatest(["M",xa,xb],["Mc",xc,xa,xb^-1]),
thetatest(["M",xa,xb],["Mc",xc,xa^-1,xb^-1]),
thetatest(["M",xa,xb],["Mc",xc,xb,xa]),
thetatest(["M",xa,xb],["Mc",xc,xb^-1,xa]),
thetatest(["M",xa,xb],["Mc",xc,xb,xa^-1]),
thetatest(["M",xa,xb],["Mc",xc,xb^-1,xa^-1]),

thetatest(["M",xa,xb^-1],["C",xc,xd]),
thetatest(["M",xa,xb^-1],["C",xa,xd]),
thetatest(["M",xa,xb^-1],["C",xc,xa]),
thetatest(["M",xa,xb^-1],["C",xc,xa^-1]),
thetatest(["M",xa,xb^-1],["C",xb^-1,xd]),
thetatest(["M",xa,xb^-1],["C",xc,xb^-1]),
thetatest(["M",xa,xb^-1],["C",xc,xb]),
thetatest(["M",xa,xb^-1],["C",xa,xb^-1]),
thetatest(["M",xa,xb^-1],["C",xa,xb]),
thetatest(["M",xa,xb^-1],["C",xb^-1,xa]),
thetatest(["M",xa,xb^-1],["C",xb^-1,xa^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xd,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa,xd,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa^-1,xd,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xd,xa]),
thetatest(["M",xa,xb^-1],["Mc",xc,xd,xa^-1]),
thetatest(["M",xa,xb^-1],["Mc",xb^-1,xd,xe]),
thetatest(["M",xa,xb^-1],["Mc",xb,xd,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb,xe]),
thetatest(["M",xa,xb^-1],["Mc",xc,xd,xb^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xd,xb]),
thetatest(["M",xa,xb^-1],["Mc",xa,xb^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa,xb,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa^-1,xb^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa^-1,xb,xe]),
thetatest(["M",xa,xb^-1],["Mc",xa,xd,xb^-1]),
thetatest(["M",xa,xb^-1],["Mc",xa^-1,xd,xb^-1]),
thetatest(["M",xa,xb^-1],["Mc",xa,xd,xb]),
thetatest(["M",xa,xb^-1],["Mc",xa^-1,xd,xb]),
thetatest(["M",xa,xb^-1],["Mc",xb^-1,xa,xe]),
thetatest(["M",xa,xb^-1],["Mc",xb,xa,xe]),
thetatest(["M",xa,xb^-1],["Mc",xb^-1,xa^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xb,xa^-1,xe]),
thetatest(["M",xa,xb^-1],["Mc",xb^-1,xd,xa]),
thetatest(["M",xa,xb^-1],["Mc",xb,xd,xa]),
thetatest(["M",xa,xb^-1],["Mc",xb^-1,xd,xa^-1]),
thetatest(["M",xa,xb^-1],["Mc",xb,xd,xa^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa,xb^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa^-1,xb^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa,xb]),
thetatest(["M",xa,xb^-1],["Mc",xc,xa^-1,xb]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb^-1,xa]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb,xa]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb^-1,xa^-1]),
thetatest(["M",xa,xb^-1],["Mc",xc,xb,xa^-1]),

thetatest(["M",xa^-1,xb],["C",xc,xd]),
thetatest(["M",xa^-1,xb],["C",xa^-1,xd]),
thetatest(["M",xa^-1,xb],["C",xc,xa^-1]),
thetatest(["M",xa^-1,xb],["C",xc,xa]),
thetatest(["M",xa^-1,xb],["C",xb,xd]),
thetatest(["M",xa^-1,xb],["C",xc,xb]),
thetatest(["M",xa^-1,xb],["C",xc,xb^-1]),
thetatest(["M",xa^-1,xb],["C",xa^-1,xb]),
thetatest(["M",xa^-1,xb],["C",xa^-1,xb^-1]),
thetatest(["M",xa^-1,xb],["C",xb,xa^-1]),
thetatest(["M",xa^-1,xb],["C",xb,xa]),
thetatest(["M",xa^-1,xb],["Mc",xc,xd,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa^-1,xd,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa,xd,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xd,xa^-1]),
thetatest(["M",xa^-1,xb],["Mc",xc,xd,xa]),
thetatest(["M",xa^-1,xb],["Mc",xb,xd,xe]),
thetatest(["M",xa^-1,xb],["Mc",xb^-1,xd,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xc,xd,xb]),
thetatest(["M",xa^-1,xb],["Mc",xc,xd,xb^-1]),
thetatest(["M",xa^-1,xb],["Mc",xa^-1,xb,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa^-1,xb^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa,xb,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa,xb^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xa^-1,xd,xb]),
thetatest(["M",xa^-1,xb],["Mc",xa,xd,xb]),
thetatest(["M",xa^-1,xb],["Mc",xa^-1,xd,xb^-1]),
thetatest(["M",xa^-1,xb],["Mc",xa,xd,xb^-1]),
thetatest(["M",xa^-1,xb],["Mc",xb,xa^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xb^-1,xa^-1,xe]),
thetatest(["M",xa^-1,xb],["Mc",xb,xa,xe]),
thetatest(["M",xa^-1,xb],["Mc",xb^-1,xa,xe]),
thetatest(["M",xa^-1,xb],["Mc",xb,xd,xa^-1]),
thetatest(["M",xa^-1,xb],["Mc",xb^-1,xd,xa^-1]),
thetatest(["M",xa^-1,xb],["Mc",xb,xd,xa]),
thetatest(["M",xa^-1,xb],["Mc",xb^-1,xd,xa]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa^-1,xb]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa,xb]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa^-1,xb^-1]),
thetatest(["M",xa^-1,xb],["Mc",xc,xa,xb^-1]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb,xa^-1]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb^-1,xa^-1]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb,xa]),
thetatest(["M",xa^-1,xb],["Mc",xc,xb^-1,xa]),


thetatest(["M",xa^-1,xb^-1],["C",xc,xd]),
thetatest(["M",xa^-1,xb^-1],["C",xa^-1,xd]),
thetatest(["M",xa^-1,xb^-1],["C",xc,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["C",xc,xa]),
thetatest(["M",xa^-1,xb^-1],["C",xb^-1,xd]),
thetatest(["M",xa^-1,xb^-1],["C",xc,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["C",xc,xb]),
thetatest(["M",xa^-1,xb^-1],["C",xa^-1,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["C",xa^-1,xb]),
thetatest(["M",xa^-1,xb^-1],["C",xb^-1,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["C",xb^-1,xa]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xd,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa^-1,xd,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa,xd,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xd,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xd,xa]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb^-1,xd,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb,xd,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xd,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xd,xb]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa^-1,xb^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa^-1,xb,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa,xb^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa,xb,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa^-1,xd,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa,xd,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa^-1,xd,xb]),
thetatest(["M",xa^-1,xb^-1],["Mc",xa,xd,xb]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb^-1,xa^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb,xa^-1,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb^-1,xa,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb,xa,xe]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb^-1,xd,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb,xd,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb^-1,xd,xa]),
thetatest(["M",xa^-1,xb^-1],["Mc",xb,xd,xa]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa^-1,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa,xb^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa^-1,xb]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xa,xb]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb^-1,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb,xa^-1]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb^-1,xa]),
thetatest(["M",xa^-1,xb^-1],["Mc",xc,xb,xa]),
];




#verifying that extra relations for IA_n follow from listed relations.

exiarelchecklist:=
[
applyrels(exiarel(1,[xa,xb,xc]),[[3,iarel(9,[xa,xb^-1,xc,xb])],[1,iarel(5,[xc,xb,xa])]]),
applyrels(exiarel(2,[xa,xb,xc,xd,xe]),[[2,iw(iarel(5,[xd,xa,xe]))],[4,cyw(-2,iarel(7,[xd,xa,xb,xc]))],[1,iw(cyw(-2,iarel(7,[xd,xa,xb,xc])))],[8,iarel(8,[xa,xb,xc,xd,xe])],[14,iw(iarel(6,[xd,xb,xc]))],[7,theta([["M",xd,xe^-1]],iarel(2,[xd^-1,xc,xb,xd,xb,xc]))],[6,iarel(2,[xd^-1,xc,xb,xd,xe,xa])],[5,iarel(2,[xd^-1,xc,xb,xd,xc,xb])],[7,iarel(6,[xd,xb,xc])],[3,iarel(5,[xd,xa,xe])]]),
applyrels(exiarel(2,[xa,xb,xc,xd,xb]),[[2,iw(iarel(5,[xd,xa,xb]))],[4,cyw(-2,iarel(7,[xd,xa,xb,xc]))],[1,iw(cyw(-2,iarel(7,[xd,xa,xb,xc])))],[8,iarel(8,[xa,xb,xc,xd,xb])],[12,iw(iarel(6,[xd,xb,xc]))],[7,theta([["M",xd,xb^-1]],iarel(2,[xd^-1,xc,xb,xd,xb,xc]))],[6,iarel(2,[xd^-1,xc,xb,xd,xb,xa])],[5,iarel(2,[xd^-1,xc,xb,xd,xc,xb])],[7,iarel(6,[xd,xb,xc])],[3,iarel(5,[xd,xa,xb])]]),
applyrels(exiarel(2,[xa,xb,xc,xd,xb^-1]),[[2,iw(iarel(5,[xd,xa,xb^-1]))],[4,cyw(-2,iarel(7,[xd,xa,xb,xc]))],[1,iw(cyw(-2,iarel(7,[xd,xa,xb,xc])))],[8,iarel(8,[xa,xb,xc,xd,xb^-1])],[14,iw(iarel(6,[xd,xb,xc]))],[7,theta([["M",xd,xb]],iarel(2,[xd^-1,xc,xb,xd,xb,xc]))],[6,iarel(2,[xd^-1,xc,xb,xd,xb^-1,xa])],[5,iarel(2,[xd^-1,xc,xb,xd,xc,xb])],[7,iarel(6,[xd,xb,xc])],[3,iarel(5,[xd,xa,xb^-1])]]),
applyrels(exiarel(2,[xa,xb,xc,xd,xc]),[[2,iw(iarel(5,[xd,xa,xc]))],[4,cyw(-2,iarel(7,[xd,xa,xb,xc]))],[1,iw(cyw(-2,iarel(7,[xd,xa,xb,xc])))],[8,iarel(8,[xa,xb,xc,xd,xc])],[14,iw(iarel(6,[xd,xb,xc]))],[7,theta([["M",xd,xc^-1]],iarel(2,[xd^-1,xc,xb,xd,xb,xc]))],[6,iarel(2,[xd^-1,xc,xb,xd,xc,xa])],[5,iarel(2,[xd^-1,xc,xb,xd,xc,xb])],[7,iarel(6,[xd,xb,xc])],[3,iarel(5,[xd,xa,xc])]]),
applyrels(exiarel(2,[xa,xb,xc,xd,xc^-1]),[[2,iw(iarel(5,[xd,xa,xc^-1]))],[4,cyw(-2,iarel(7,[xd,xa,xb,xc]))],[1,iw(cyw(-2,iarel(7,[xd,xa,xb,xc])))],[8,iarel(8,[xa,xb,xc,xd,xc^-1])],[14,iw(iarel(6,[xd,xb,xc]))],[7,theta([["M",xd,xc]],iarel(2,[xd^-1,xc,xb,xd,xb,xc]))],[6,iarel(2,[xd^-1,xc,xb,xd,xc^-1,xa])],[5,iarel(2,[xd^-1,xc,xb,xd,xc,xb])],[7,iarel(6,[xd,xb,xc])],[3,iarel(5,[xd,xa,xc^-1])]]),
applyrels(exiarel(3,[xa,xb,xc,xd]),[[5,cyw(1,theta([["M",xa,xd]],iarel(6,[xa,xb,xc])))],[16,iarel(1,[xa,xd^-1,xb,xd^-1])],[15,iarel(1,[xa,xd^-1,xc,xd^-1])],[1,iarel(1,[xb,xd,xa,xd])],[2,iarel(1,[xc,xd,xa,xd])],[2,iarel(9,[xb,xd^-1,xa,xc])],[5,iarel(3,[xa,xd^-1,xb,xc,xd])],[6,iarel(2,[xa^-1,xb,xc,xa,xd^-1,xb])],[6,cyw(-3,iw(iarel(9,[xc,xd^-1,xa,xb])))],[9,iw(iarel(5,[xa^-1,xb,xc]))],[8,iarel(2,[xa^-1,xc,xb^-1,xa,xd^-1,xc])],[8,iarel(5,[xa^-1,xb,xc])],[8,iarel(6,[xa^-1,xc,xb])],[5,iarel(4,[xc^-1,xd^-1,xa])],[2,iarel(3,[xa,xb,xd^-1,xc,xd])],[5,iarel(5,[xa,xd^-1,xb])],[3,iarel(4,[xc,xd^-1,xa])],[7,iw(iarel(6,[xa,xc,xd^-1]))],[6,theta([["M",xa^-1,xc]],iarel(2,[xa,xd^-1,xb,xa^-1,xd^-1,xc]))],[7,iw(iarel(5,[xa,xd,xb]))],[8,iarel(6,[xa,xc,xd^-1])]]),
applyrels(exiarel(4,[xa,xb,xc,xd]),[[3,exiarel(3,[xa,xc,xd,xb])],[5,iarel(9,[xd,xb,xa,xc])],[6,iarel(3,[xa,xb,xd,xc,xb^-1])],[5,cyw(-1,iw(iarel(9,[xc,xb,xa,xd])))],[6,iarel(4,[xc^-1,xb,xa])],[1,iw(iarel(4,[xc^-1,xb,xa]))],[5,iarel(3,[xa,xd,xb,xc,xb^-1])],[1,iarel(6,[xa,xc,xb])],[1,iw(iarel(5,[xa^-1,xc^-1,xb]))],[1,iarel(2,[xa,xd,xb,xa^-1,xb,xc^-1])],[7,iw(iarel(5,[xa,xc^-1,xb]))],[3,iarel(6,[xa^-1,xc^-1,xb])]]),
applyrels(exiarel(5,[xa,xb,xc,xd,xa,xb]),[[2,iarel(1,[xa,xb,xc,xd])],[1,iw(iarel(4,[xb,xd,xa]))]]),
#other cases for exiarel(5) are similar.
applyrels(exiarel(6,[xa,xb,xc]),[[2,cyw(9,theta([["M",xa,xb^-1]],iarel(6,[xb^-1,xa,xc])))],[1,iw(iarel(4,[xc,xa,xb]))],[2,iarel(4,[xb,xa^-1,xc])],[8,iarel(5,[xa,xc,xb])],[7,iarel(1,[xa,xc,xb,xc])],[9,iw(exiarel(1,[xa,xc,xb]))],[10,iw(exiarel(1,[xc,xa,xb]))],[10,iw(iarel(4,[xb,xa^-1,xc]))],[9,exiarel(1,[xc,xb,xa^-1])],[8,exiarel(1,[xb^-1,xc,xa^-1])],[7,iarel(4,[xb,xc^-1,xa])],[3,iarel(5,[xa,xb^-1,xc^-1])],[3,iarel(6,[xa,xc^-1,xb^-1])]]),
applyrels(exiarel(7,[xa,xb,xc]),[[10,iw(iarel(6,[xa,xb,xc]))],[18,cyw(2,exiarel(6,[xa,xb,xc]))],[9,iarel(4,[xc^-1,xb,xa^-1])],[9,iarel(1,[xa^-1,xb^-1,xc,xb^-1])],[11,iarel(4,[xc,xb,xa^-1])],[6,iarel(1,[xa^-1,xc^-1,xb^-1,xc^-1])],[8,iarel(4,[xb^-1,xc,xa^-1])],[8,iw(iarel(4,[xc,xb^-1,xa]))],[4,iarel(1,[xc,xb,xa,xb])],[2,iarel(1,[xb,xc,xa,xc])]]),
applyrels(exiarel(8,[xa,xb,xc,xd]),[[17,iw(iarel(7,[xd,xa,xb,xc]))],[16,iw(exiarel(7,[xa,xb,xc]))],[6,iw(exiarel(5,[xd,xb,xa,xc^-1,xd,xb^-1]))],[7,iarel(4,[xc,xb,xd])],[0,iw(exiarel(5,[xa,xb,xd,xc,xa,xb]))],[1,iw(exiarel(5,[xa,xb,xd,xc,xd,xb^-1]))],[0,iarel(1,[xd,xb^-1,xa,xb])],[3,iw(iarel(4,[xb^-1,xc,xa]))],[3,iarel(1,[xd,xb,xa,xb])],[2,iw(iarel(4,[xb,xc,xd]))],[4,iarel(1,[xa,xc^-1,xd,xc])],[5,exiarel(5,[xb,xc,xd,xa,xd,xc])],[3,iarel(1,[xa,xc^-1,xd,xb])],[4,exiarel(5,[xb,xc,xd,xa,xd,xb])],[2,iarel(1,[xa,xc^-1,xd,xc^-1])],[1,exiarel(5,[xb,xc,xd,xa,xd,xc^-1])],[0,exiarel(5,[xb,xc,xd,xa,xd,xb^-1])]])
];




# verifying that acting by a generator, immediately followed by its inverse, under theta, is trivial in the L-presentation for IA_n

thetainversecheck :=function(by,on)
	return pw(theta([by,invertmove(by)],[on]),iw([on]));
end;
thetainverselist :=
[
thetainversecheck(["M",xa,xb],["C",xc,xd]),
#thetainversecheck(["M",xa,xb],["C",xa,xd]),
	applyrels(pw(theta([[ "M", xa, xb ],[ "M", xa, xb^-1]], [[ "C", xa, xd ]]),[["C",xa,xd^-1]]),[[2,iw(iarel(5,[xa,xb,xd]))]]),
thetainversecheck(["M",xa,xb],["C",xc,xa]),
#thetainversecheck(["M",xa,xb],["C",xb,xd]),
	applyrels(pw(theta([[ "M", xa, xb ],[ "M", xa, xb^-1]], [[ "C", xb, xd ]]),[["C",xb,xd^-1]]),[[2,iw(iarel(5,[xa,xb,xd^-1]))]]),
thetainversecheck(["M",xa,xb],["C",xc,xb]),
thetainversecheck(["M",xa,xb],["C",xa,xb]),
thetainversecheck(["M",xa,xb],["C",xb,xa]),
thetainversecheck(["M",xa,xb],["Mc",xc,xd,xe]),
thetainversecheck(["M",xa,xb],["Mc",xa,xd,xe]),
#thetainversecheck(["M",xa,xb],["Mc",xc,xa,xe]),
	applyrels(pw(theta([[ "M", xa, xb ],[ "M", xa, xb^-1]], [[ "Mc", xc, xa, xe ]]),[[ "Mc", xc, xe, xa ]]),[[1,iw(iarel(5,[xc,xb,xe]))]]),
#thetainversecheck(["M",xa,xb],["Mc",xb,xd,xe]),
	applyrels(pw(theta([[ "M", xa, xb ],[ "M", xa, xb^-1]], [[ "Mc", xb, xd, xe ]]),[[ "Mc", xb, xe, xd ]]),[[3,iarel(7,[xa,xb,xd,xe])],[3,iarel(6,[xa^-1,xe,xd])]]),
thetainversecheck(["M",xa,xb],["Mc",xc,xb,xe]),
thetainversecheck(["M",xa,xb],["Mc",xa,xb,xe]),
#thetainversecheck(["M",xa,xb],["Mc",xb,xa,xe]),
	applyrels(pw(theta([[ "M", xa, xb ],[ "M", xa, xb^-1]], [[ "Mc", xb, xa, xe ]]),[[ "Mc", xb, xe, xa ]]),[[6,iarel(5,[xa,xb,xe])],[6,iw(exiarel(1,[xb^-1,xe,xa]))],[2,iw(iarel(4,[xe,xa,xb]))],[2,iarel(6,[xb^-1,xe^-1,xa])],[2,iw(iarel(5,[xb,xe,xa]))]]),
thetainversecheck(["M",xa,xb],["Mc",xc,xa,xb])
];


# Verifying that the action of Nielsen's relations on the L-presentation for IA_n via theta is always trivial:


thetaN3check:=function(la,lb,on)
	return pw(theta([["M",lb,la],["M",la,lb^-1]],[on]),iw(theta([["M",la^-1,lb^-1],["I",lb],["P",la,lb]],[on])));
end;

thetaN3list:=
[
thetaN3check(xa,xb,["C",xc,xd]),
#thetaN3check(xa,xb,["C",xa,xd]),
	applyrels(thetaN3check(xa,xb,["C",xa,xd]),[[1,iarel(5,[xb,xd,xa^-1])],[0,iarel(1,[xb,xd,xa,xd])]]),
thetaN3check(xa,xb,["C",xc,xa]),
#thetaN3check(xa,xb,["C",xb,xd]),
	applyrels(thetaN3check(xa,xb,["C",xb,xd]),[[3,iarel(5,[xb,xd,xa^-1])]]),
thetaN3check(xa,xb,["C",xc,xb]),

thetaN3check(xa,xb,["Mc",xc,xd,xe]),
#thetaN3check(xa,xb,["Mc",xa,xd,xe]),
	applyrels(thetaN3check(xa,xb,["Mc",xa,xd,xe]),[[1,iarel(2,[xa,xd,xe,xb^-1,xd,xe])]]),
#thetaN3check(xa,xb,["Mc",xc,xa,xe]),
	applyrels(thetaN3check(xa,xb,["Mc",xc,xa,xe]),[[3,iw(iarel(5,[xc,xa,xe]))]]),
#thetaN3check(xa,xb,["Mc",xb,xd,xe]),
	applyrels(thetaN3check(xa,xb,["Mc",xb,xd,xe]),[[1,iarel(2,[xa,xd,xe,xb^-1,xd,xe])],[4,iarel(6,[xb,xe,xd])],[2,iw(iarel(7,[xb,xa,xe,xd]))]]),
thetaN3check(xa,xb,["Mc",xc,xb,xe]),
#thetaN3check(xa,xb,["Mc",xa,xb,xe]),
	applyrels(thetaN3check(xa,xb,["Mc",xa,xb,xe]),[[0,theta([["M",xb,xa]],iarel(9,[xe,xb,xa,xb]))],[5,iarel(5,[xa^-1,xe,xb])],[5,iarel(5,[xb,xe,xa^-1])]]),
#thetaN3check(xa,xb,["Mc",xb,xa,xe]),
	applyrels(thetaN3check(xa,xb,["Mc",xb,xa,xe]),[[6,iw(iarel(9,[xe,xa^-1,xb,xa^-1]))],[0,exiarel(1,[xa^-1,xe,xb])],[3,iw(exiarel(1,[xe^-1,xb^-1,xa^-1]))],[2,iw(iarel(4,[xe,xb^-1,xa]))],[1,iarel(5,[xa^-1,xe,xb^-1])],[1,iarel(6,[xa^-1,xb^-1,xe])]]),
thetaN3check(xa,xb,["Mc",xc,xa,xb])
];


thetaN4check:= function(xxa,xxb,xxc,xxd,on)
	return pw(theta([["M",xxa,xxb],["M",xxc,xxd]],[on]),theta([["M",xxc,xxd],["M",xxa,xxb]],iw([on])));
end;

thetaN4list:=
[
thetaN4check(xa,xb,xc,xd,["C",xe,xf]),
thetaN4check(xa,xb,xc,xd,["C",xa,xf]),
thetaN4check(xa,xb,xc,xd,["C",xe,xa]),
thetaN4check(xa,xb,xc,xd,["C",xb,xf]),
thetaN4check(xa,xb,xc,xd,["C",xe,xb]),
thetaN4check(xa,xb,xc,xd,["C",xa,xb]),
thetaN4check(xa,xb,xc,xd,["C",xb,xa]),
thetaN4check(xa,xb,xc,xd,["C",xa,xc]),
thetaN4check(xa,xb,xc,xd,["C",xa,xd]),
#thetaN4check(xa,xb,xc,xd,["C",xd,xa]),
	applyrels(thetaN4check(xa,xb,xc,xd,["C",xd,xa]),[[9,iw(cyw(2,iarel(9,[xd^-1,xb^-1,xc,xa^-1])))]]),
thetaN4check(xa,xb,xc,xd,["C",xb,xd]),

thetaN4check(xa,xb,xc,xd,["Mc",xe,xf,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xa,xf,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xe,xa,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xb,xf,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xe,xb,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xa,xb,xg]),
thetaN4check(xa,xb,xc,xd,["Mc",xb,xa,xg]),
#thetaN4check(xa,xb,xc,xd,["Mc",xa,xc,xg]),
	applyrels(thetaN4check(xa,xb,xc,xd,["Mc",xa,xc,xg]),[[4,iarel(6,[xa,xb^-1,xd])],[4,iw(iarel(5,[xa^-1,xb,xd]))],[3,iw(iarel(5,[xa^-1,xd^-1,xb]))],[3,iarel(2,[xa,xc,xg,xa^-1,xb,xd^-1])],[5,iw(iarel(5,[xa^-1,xb^-1,xd^-1]))],[6,iw(iarel(5,[xa^-1,xd,xb^-1]))],[8,iarel(6,[xa,xd,xb^-1])]]),
thetaN4check(xa,xb,xc,xd,["Mc",xa,xd,xg]),
#thetaN4check(xa,xb,xc,xd,["Mc",xd,xa,xg]),
	applyrels(thetaN4check(xa,xb,xc,xd,["Mc",xd,xa,xg]),[[10,iarel(5,[xc,xd,xb^-1])],[10,iw(exiarel(1,[xd,xb,xc]))],[12,iarel(4,[xd,xb,xc])],[9,iarel(6,[xc,xd,xb])],[7,iw(iarel(8,[xd,xa,xg,xc^-1,xb]))],[14,iw(exiarel(1,[xd^-1,xb,xc]))],[12,iarel(5,[xc,xd,xb])],[12,iarel(6,[xc,xb,xd])],[11,iw(iarel(4,[xd,xb,xc]))],[6,iarel(1,[xc,xb^-1,xd,xb^-1])],[8,iarel(3,[xc^-1,xg,xa,xd,xb])],[8,iarel(1,[xc,xb,xd,xb^-1])],[5,iarel(3,[xd,xb,xg,xc,xb^-1])],[3,iarel(2,[xd,xb,xg,xc^-1,xa,xg])],[3,iarel(3,[xd,xb,xg,xc,xb])]]),
thetaN4check(xa,xb,xc,xd,["Mc",xd,xb,xg]),

thetaN4check(xa,xb,xc,xb,["C",xe,xf]),
thetaN4check(xa,xb,xc,xb,["C",xa,xf]),
thetaN4check(xa,xb,xc,xb,["C",xe,xa]),
#thetaN4check(xa,xb,xc,xb,["C",xb,xf]),
	applyrels(thetaN4check(xa,xb,xc,xb,["C",xb,xf]),[[1,iarel(2,[xc,xb^-1,xf^-1,xa,xb^-1,xf^-1])]]),
thetaN4check(xa,xb,xc,xb,["C",xe,xb]),
thetaN4check(xa,xb,xc,xb,["C",xa,xb]),
thetaN4check(xa,xb,xc,xb,["C",xb,xa]),
#thetaN4check(xa,xb,xc,xb,["C",xa,xc]),
	applyrels(thetaN4check(xa,xb,xc,xb,["C",xa,xc]),[[2,iw(iarel(5,[xa,xb,xc]))]]),

thetaN4check(xa,xb,xc,xb,["Mc",xe,xf,xg]),
thetaN4check(xa,xb,xc,xb,["Mc",xa,xf,xg]),
thetaN4check(xa,xb,xc,xb,["Mc",xe,xa,xg]),
#thetaN4check(xa,xb,xc,xb,["Mc",xb,xf,xg]),
	applyrels(thetaN4check(xa,xb,xc,xb,["Mc",xb,xf,xg]),[[5,iarel(1,[xc,xb^-1,xa,xb^-1])],[6,iarel(3,[xa^-1,xg,xf,xc,xb])],[3,iarel(2,[xc^-1,xg,xf,xa^-1,xf,xg])],[1,iarel(3,[xc^-1,xf,xg,xa,xb])],[0,iarel(1,[xa,xb,xc,xb])]]),
thetaN4check(xa,xb,xc,xb,["Mc",xe,xb,xg]),
thetaN4check(xa,xb,xc,xb,["Mc",xa,xb,xg]),
#thetaN4check(xa,xb,xc,xb,["Mc",xb,xa,xg]),
	applyrels(thetaN4check(xa,xb,xc,xb,["Mc",xb,xa,xg]),[[10,cyw(4,iarel(7,[xc,xb^-1,xg^-1,xa]))],[10,iarel(6,[xc^-1,xa,xg^-1])],[9,iarel(2,[xc^-1,xa,xg^-1,xb^-1,xa,xg^-1])],[8,iarel(9,[xb^-1,xg,xa,xg])],[9,iarel(1,[xc,xb^-1,xa,xg])],[12,iw(exiarel(1,[xa,xg,xc^-1]))],[5,iarel(1,[xb,xg^-1,xa,xg])],[6,iarel(3,[xa,xb^-1,xg,xc,xb^-1])],[10,iarel(2,[xc,xa,xg^-1,xb^-1,xa,xg^-1])],[9,iarel(1,[xb,xg,xa,xg])],[11,iarel(3,[xc,xb^-1,xg^-1,xa,xg^-1])],[11,iw(iarel(5,[xa,xg,xb^-1]))],[9,cyw(1,iarel(8,[xa,xb^-1,xg,xc^-1,xg]))],[13,iw(exiarel(1,[xb^-1,xg^-1,xa]))],[13,iarel(2,[xc,xb^-1,xg^-1,xa,xg^-1,xb^-1])],[13,cyw(-1,iw(iarel(9,[xb^-1,xg,xc^-1,xg])))],[8,iarel(3,[xc^-1,xg,xa,xb,xg])],[7,exiarel(1,[xb^-1,xg^-1,xc^-1])],[8,iarel(4,[xb,xg^-1,xc])],[4,iarel(6,[xc,xg^-1,xb^-1])],[3,iarel(2,[xc,xg^-1,xb^-1,xc^-1,xa,xg])],[3,iarel(2,[xc^-1,xb^-1,xg,xc,xg^-1,xb^-1])],[0,iw(iarel(5,[xc^-1,xb,xg]))]]),
thetaN4check(xa,xb,xc,xb,["Mc",xa,xc,xg]),

thetaN4check(xa,xb,xc,xb^-1,["C",xe,xf]),
thetaN4check(xa,xb,xc,xb^-1,["C",xa,xf]),
thetaN4check(xa,xb,xc,xb^-1,["C",xe,xa]),
#thetaN4check(xa,xb,xc,xb^-1,["C",xb,xf]),
	applyrels(thetaN4check(xa,xb,xc,xb^-1,["C",xb,xf]),[[1,iarel(2,[xc,xb,xf^-1,xa,xb^-1,xf^-1])]]),
thetaN4check(xa,xb,xc,xb^-1,["C",xe,xb]),
thetaN4check(xa,xb,xc,xb^-1,["C",xa,xb]),
thetaN4check(xa,xb,xc,xb^-1,["C",xb,xa]),
#thetaN4check(xa,xb,xc,xb^-1,["C",xa,xc]),
	applyrels(thetaN4check(xa,xb,xc,xb^-1,["C",xa,xc]),[[5,cyw(1,iarel(9,[xc,xb^-1,xa,xb^-1]))]]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xe,xf,xg]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xa,xf,xg]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xe,xa,xg]),
#thetaN4check(xa,xb,xc,xb^-1,["Mc",xb,xf,xg]),
	applyrels(thetaN4check(xa,xb,xc,xb^-1,["Mc",xb,xf,xg]),[[2,iarel(2,[xc,xg,xf,xa^-1,xf,xg])],[0,iarel(3,[xc,xf,xg,xa,xb])]]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xe,xb,xg]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xa,xb,xg]),
#thetaN4check(xa,xb,xc,xb^-1,["Mc",xb,xa,xg]),
	applyrels(thetaN4check(xa,xb,xc,xb^-1,["Mc",xb,xa,xg]),[[9,cyw(4,iarel(7,[xc,xb^-1,xg^-1,xa]))],[9,iarel(6,[xc,xa,xg^-1])],[8,iarel(2,[xc,xa,xg^-1,xb^-1,xa,xg^-1])],[7,iarel(9,[xb^-1,xg,xa,xg])],[4,iarel(1,[xb,xg^-1,xa,xg])],[6,iarel(1,[xc,xb^-1,xa,xg])],[9,iw(exiarel(1,[xa,xg,xc]))],[9,iarel(2,[xc^-1,xa,xg^-1,xb^-1,xa,xg^-1])],[8,iarel(1,[xc,xb,xa,xg])],[9,iarel(1,[xb,xg,xa,xg])],[11,iarel(3,[xc,xb,xg^-1,xa,xg^-1])],[13,iw(iarel(5,[xa,xg^-1,xb^-1]))],[5,iarel(3,[xa,xb^-1,xg,xc,xb^-1])],[8,cyw(1,iarel(8,[xa,xb^-1,xg,xc,xg]))],[11,iarel(3,[xa,xb^-1,xg,xc,xb])],[13,iw(exiarel(1,[xb^-1,xg^-1,xa]))],[13,iarel(2,[xc,xb,xg^-1,xa,xg^-1,xb^-1])],[14,iw(exiarel(1,[xb,xg,xc]))],[5,iarel(4,[xb^-1,xg,xc])],[2,iarel(3,[xc,xa,xg,xb,xg^-1])],[3,iarel(4,[xb,xg,xc])],[2,iarel(9,[xb,xg,xc,xg])],[5,iarel(5,[xc,xg^-1,xa])],[9,iarel(6,[xc,xb^-1,xg])],[9,iw(iarel(5,[xc^-1,xb,xg]))],[6,iw(iarel(5,[xc^-1,xg,xb]))],[5,iw(iarel(5,[xc^-1,xb,xg^-1]))],[6,iw(iarel(5,[xc,xg,xa]))],[4,iarel(2,[xc^-1,xg^-1,xb^-1,xc,xg^-1,xa])],[3,iw(iarel(5,[xc,xb^-1,xg]))],[3,iarel(2,[xc^-1,xg^-1,xb^-1,xc,xg,xb^-1])],[4,iw(iarel(5,[xc^-1,xg,xb^-1]))],[5,iw(iarel(5,[xc^-1,xb,xg]))],[1,iarel(6,[xc,xb,xg])]]),
thetaN4check(xa,xb,xc,xb^-1,["Mc",xa,xc,xg]),

thetaN4check(xa,xb,xa^-1,xd,["C",xe,xf]),
#thetaN4check(xa,xb,xa^-1,xd,["C",xa,xf]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["C",xa,xf]),[[1,iarel(2,[xa^-1,xd^-1,xf,xa,xb^-1,xf])]]),
thetaN4check(xa,xb,xa^-1,xd,["C",xe,xa]),
thetaN4check(xa,xb,xa^-1,xd,["C",xb,xf]),
thetaN4check(xa,xb,xa^-1,xd,["C",xe,xb]),
thetaN4check(xa,xb,xa^-1,xd,["C",xa,xb]),
#thetaN4check(xa,xb,xa^-1,xd,["C",xb,xa]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["C",xb,xa]),[[5,iw(iarel(5,[xa^-1,xb^-1,xd^-1]))],[1,iarel(6,[xa,xb^-1,xd^-1])],[8,iarel(4,[xb^-1,xd^-1,xa])]]),
thetaN4check(xa,xb,xa^-1,xd,["C",xb,xd]),

thetaN4check(xa,xb,xa^-1,xd,["Mc",xe,xf,xg]),
#thetaN4check(xa,xb,xa^-1,xd,["Mc",xa,xf,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["Mc",xa,xf,xg]),[[1,iarel(2,[xa^-1,xd^-1,xb,xa,xf,xg])]]),
thetaN4check(xa,xb,xa^-1,xd,["Mc",xe,xa,xg]),
#thetaN4check(xa,xb,xa^-1,xd,["Mc",xb,xf,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["Mc",xb,xf,xg]),[[4,cyw(1,iarel(8,[xb,xf,xg,xa^-1,xd^-1]))]]),  
thetaN4check(xa,xb,xa^-1,xd,["Mc",xe,xb,xg]),
#thetaN4check(xa,xb,xa^-1,xd,["Mc",xa,xb,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["Mc",xa,xb,xg]),[[1,iarel(2,[xa^-1,xd^-1,xb,xa,xb,xg])]]),
#thetaN4check(xa,xb,xa^-1,xd,["Mc",xb,xa,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xd,["Mc",xb,xa,xg]),[[5,iarel(2,[xb,xd^-1,xg,xa^-1,xd^-1,xg])],[6,iarel(2,[xb^-1,xg^-1,xd^-1,xa^-1,xd^-1,xg])],[7,iarel(7,[xb,xa^-1,xd^-1,xg])],[12,cyw(3,exiarel(2,[xa^-1,xd^-1,xg,xb^-1,xg^-1]))],[17,iarel(3,[xa^-1,xd^-1,xg,xb,xg])],[18,iarel(2,[xa,xg,xb^-1,xa^-1,xd^-1,xg])],[7,iarel(6,[xb,xg,xd^-1])],[5,iarel(2,[xb^-1,xg^-1,xd^-1,xb,xd^-1,xg])],[6,iw(iarel(5,[xb^-1,xg,xd^-1]))]]),

thetaN4check(xa,xb,xa^-1,xb,["C",xe,xf]),
#thetaN4check(xa,xb,xa^-1,xb,["C",xa,xf]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb,["C",xa,xf]),[[1,iarel(2,[xa^-1,xb^-1,xf,xa,xb^-1,xf])]]),
thetaN4check(xa,xb,xa^-1,xb,["C",xe,xa]),
#thetaN4check(xa,xb,xa^-1,xb,["C",xb,xf]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb,["C",xb,xf]),[[1,iarel(2,[xa^-1,xb^-1,xf^-1,xa,xb^-1,xf^-1])]]),
thetaN4check(xa,xb,xa^-1,xb,["C",xe,xb]),
thetaN4check(xa,xb,xa^-1,xb,["C",xa,xb]),
thetaN4check(xa,xb,xa^-1,xb,["C",xb,xa]),

thetaN4check(xa,xb,xa^-1,xb,["Mc",xe,xf,xg]),
thetaN4check(xa,xb,xa^-1,xb,["Mc",xa,xf,xg]),
thetaN4check(xa,xb,xa^-1,xb,["Mc",xe,xa,xg]),
#thetaN4check(xa,xb,xa^-1,xb,["Mc",xb,xf,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb,["Mc",xb,xf,xg]),[[2,iarel(2,[xa^-1,xf,xg,xa,xf,xg])]]),
thetaN4check(xa,xb,xa^-1,xb,["Mc",xe,xb,xg]),
thetaN4check(xa,xb,xa^-1,xb,["Mc",xa,xb,xg]),
#thetaN4check(xa,xb,xa^-1,xb,["Mc",xb,xa,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb,["Mc",xb,xa,xg]),[[6,iw(exiarel(1,[xg,xb,xa^-1]))],[7,iw(exiarel(1,[xg,xb,xa]))],[9,iarel(4,[xg,xb,xa])],[6,iarel(6,[xa,xg,xb])],[4,iw(exiarel(1,[xg^-1,xa,xb^-1]))],[3,iarel(4,[xg^-1,xb^-1,xa])],[5,iarel(6,[xa^-1,xb^-1,xg])]]),

thetaN4check(xa,xb,xa^-1,xb^-1,["C",xe,xf]),
thetaN4check(xa,xb,xa^-1,xb^-1,["C",xe,xf]),
#thetaN4check(xa,xb,xa^-1,xb^-1,["C",xa,xf]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb^-1,["C",xa,xf]),[[1,iarel(2,[xa^-1,xb,xf,xa,xb^-1,xf])]]),
thetaN4check(xa,xb,xa^-1,xb^-1,["C",xe,xa]),
#thetaN4check(xa,xb,xa^-1,xb^-1,["C",xb,xf]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb^-1,["C",xb,xf]),[[1,iarel(2,[xa^-1,xb,xf^-1,xa,xb^-1,xf^-1])]]),
thetaN4check(xa,xb,xa^-1,xb^-1,["C",xe,xb]),
thetaN4check(xa,xb,xa^-1,xb^-1,["C",xa,xb]),
thetaN4check(xa,xb,xa^-1,xb^-1,["C",xb,xa]),

thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,xf,xg]),
thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xa,xf,xg]),
thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,xa,xg]),
thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,xf,xg]),
#applyrels(thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,xf,xg]),[[3,iarel(7,[xa,xb,xf,xg])],[8,iarel(2,[xa^-1,xg,xf,xb,xf,xg])],[11,cyw(4,iarel(7,[xa,xb,xg,xf]))],[11,iarel(6,[xa,xf,xg])],[10,iarel(2,[xa,xf,xg,xb,xf,xg])],[3,iarel(6,[xa^-1,xg,xf])],[0,theta([["M",xa,xb]],iarel(2,[xa,xg,xf,xa^-1,xf,xg]))]]),
thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xe,xb,xg]),
thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xa,xb,xg]),
#thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,xa,xg]),
	applyrels(thetaN4check(xa,xb,xa^-1,xb^-1,["Mc",xb,xa,xg]),[[11,iarel(5,[xa,xg^-1,xb^-1])],[11,iw(exiarel(1,[xg^-1,xb,xa]))],[13,iarel(4,[xg^-1,xb,xa])],[10,iarel(6,[xa,xg^-1,xb])],[10,iarel(5,[xb,xg^-1,xa^-1])],[10,iw(exiarel(1,[xg^-1,xa,xb]))],[12,iarel(4,[xg^-1,xa,xb])],[9,iarel(6,[xb,xg^-1,xa])],[5,exiarel(1,[xg,xb,xa])],[6,iarel(4,[xg^-1,xb,xa])],[9,iw(exiarel(1,[xb,xg,xa^-1]))],[8,iarel(6,[xa^-1,xb,xg])],[1,iw(exiarel(1,[xb,xg,xa^-1]))],[2,iarel(1,[xa,xg,xb,xg^-1])],[2,iw(iarel(5,[xa,xg,xb^-1]))],[3,iw(iarel(5,[xa^-1,xg,xb]))],[0,iarel(2,[xa^-1,xg^-1,xb,xa,xg^-1,xb^-1])]])
];




thetaN5check:=function(la,lb,lc,on)
	return pw(theta([["M",lb,la],["M",lc,lb]],[on]),iw(theta([["M",lc,lb],["M",lb,la],["M",lc,la]],[on])));
end;

thetaN5list:=
[
thetaN5check(xa,xb,xc,["C",xd,xe]),
#thetaN5check(xa,xb,xc,["C",xa,xe]),
	applyrels(thetaN5check(xa,xb,xc,["C",xa,xe]),[[3,cyw(4,iarel(7,[xc,xb,xe^-1,xa^-1]))],[8,iarel(2,[xc^-1,xe^-1,xa^-1,xb,xe^-1,xa^-1])],[3,iarel(6,[xc^-1,xa^-1,xe^-1])]]),
thetaN5check(xa,xb,xc,["C",xd,xa]),
#thetaN5check(xa,xb,xc,["C",xb,xe]),
	applyrels(thetaN5check(xa,xb,xc,["C",xb,xe]),[[1,iw(exiarel(2,[xb,xa^-1,xe,xc,xe^-1]))],[8,cyw(-2,iarel(7,[xc,xb,xe,xa^-1]))],[8,iarel(6,[xc,xa^-1,xe])],[6,iarel(2,[xb,xa^-1,xe,xc,xe,xa^-1])],[6,iarel(2,[xc^-1,xa^-1,xe,xb,xa^-1,xe])],[7,iarel(2,[xc,xa^-1,xe^-1,xb,xa^-1,xe])],[6,iarel(2,[xc,xa^-1,xe^-1,xc^-1,xa^-1,xe])],[6,iarel(5,[xc,xe,xa^-1])]]),
thetaN5check(xa,xb,xc,["C",xd,xb]),
thetaN5check(xa,xb,xc,["C",xc,xe]),
thetaN5check(xa,xb,xc,["C",xd,xc]),
#thetaN5check(xa,xb,xc,["C",xa,xb]),
	applyrels(thetaN5check(xa,xb,xc,["C",xa,xb]),[[2,iarel(9,[xa^-1,xb^-1,xc,xb^-1])]]),
thetaN5check(xa,xb,xc,["C",xb,xa]),
#thetaN5check(xa,xb,xc,["C",xa,xc]),
	applyrels(thetaN5check(xa,xb,xc,["C",xa,xc]),[[7,iw(iarel(5,[xc,xa,xb^-1]))],[2,iw(iarel(5,[xb,xa,xc^-1]))],[2,exiarel(1,[xa,xc,xb])],[5,iarel(6,[xb^-1,xc,xa])],[0,iw(iarel(4,[xa,xc,xb]))]]),
thetaN5check(xa,xb,xc,["C",xc,xa]),
#thetaN5check(xa,xb,xc,["C",xb,xc]),
	applyrels(thetaN5check(xa,xb,xc,["C",xb,xc]),[[5,iarel(1,[xc,xa^-1,xb,xa^-1])],[9,iarel(9,[xb^-1,xa^-1,xc,xa^-1])],[3,exiarel(1,[xc,xa,xb])],[6,iarel(6,[xb^-1,xa,xc])],[1,iw(iarel(4,[xc,xa,xb]))]]),
#thetaN5check(xa,xb,xc,["C",xc,xb]),
	applyrels(thetaN5check(xa,xb,xc,["C",xc,xb]),[[5,iarel(5,[xc,xb,xa])]]),
#13

thetaN5check(xa,xb,xc,["Mc",xd,xe,xf]),
#thetaN5check(xa,xb,xc,["Mc",xa,xe,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xa,xe,xf]),[[8,iw(exiarel(1,[xb^-1,xa,xc]))],[9,exiarel(1,[xb^-1,xa,xc])],[10,iarel(2,[xc^-1,xf,xe,xc,xb^-1,xa])],[3,iarel(1,[xc,xa,xb,xa^-1])],[1,iarel(2,[xa,xe,xf,xb^-1,xe,xf])],[6,iarel(2,[xb^-1,xe,xf,xa,xe,xf])],[2,iarel(3,[xb^-1,xe,xf,xc,xa])],[6,iarel(3,[xc^-1,xf,xe,xb,xa])],[6,iarel(1,[xc,xa^-1,xb,xa^-1])],[4,iw(iarel(7,[xc,xa,xe,xf]))],[8,iarel(6,[xc^-1,xe,xf])]]),
thetaN5check(xa,xb,xc,["Mc",xd,xa,xf]),
#thetaN5check(xa,xb,xc,["Mc",xb,xe,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xb,xe,xf]),[[7,theta([["M",xb,xa]],iarel(3,[xb,xf,xe,xc,xa]))],[10,iw(iarel(5,[xc,xb,xa^-1]))],[9,iarel(4,[xb,xa^-1,xc])],[6,iarel(6,[xc^-1,xb,xa^-1])],[5,iw(iarel(8,[xb,xe,xf,xc^-1,xa^-1]))],[3,iarel(1,[xb,xa,xc,xa^-1])],[4,iarel(3,[xc^-1,xf,xe,xb,xa^-1])],[1,iarel(1,[xb,xa,xc,xa])],[3,iw(iarel(5,[xc^-1,xb^-1,xa^-1]))],[5,iarel(6,[xc,xb^-1,xa^-1])],[2,iarel(4,[xb^-1,xa^-1,xc])]]),
thetaN5check(xa,xb,xc,["Mc",xd,xb,xf]),
#thetaN5check(xa,xb,xc,["Mc",xc,xe,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xc,xe,xf]),[[7,iw(iarel(5,[xc,xb,xa]))],[3,iarel(6,[xc^-1,xb,xa])],[2,iarel(2,[xc^-1,xb,xa,xc,xe,xf])],[4,iarel(5,[xc,xb,xa])],[4,iarel(6,[xc,xa,xb])]]),
thetaN5check(xa,xb,xc,["Mc",xd,xc,xf]),
#thetaN5check(xa,xb,xc,["Mc",xa,xb,xf]),
	applyrels(pw(theta([["M",xb,xa],["M",xc,xb]],[["Mc",xa,xb,xf]]),theta([["M",xc,xb]],iw(applyrels(theta([["M",xb,xa]],applyrels(theta([["M",xc,xa]],[["Mc",xa,xb,xf]]),[[2,iarel(7,[xc,xa,xb,xf])],[2,iarel(6,[xc^-1,xf,xb])]])),[[4,iarel(5,[xc,xa,xf])]])))),[[4,iw(iarel(7,[xc,xb,xa^-1,xf]))],[9,iw(iarel(4,[xb,xf^-1,xc]))],[13,iarel(3,[xc,xf,xa^-1,xb,xf])],[13,iw(exiarel(1,[xb,xf,xc]))],[14,iw(iarel(4,[xb^-1,xf^-1,xc]))],[9,iarel(6,[xc,xb^-1,xf^-1])],[9,iw(iarel(5,[xc^-1,xb,xf^-1]))],[7,iarel(2,[xc,xf,xa^-1,xc^-1,xf^-1,xb])],[8,iarel(6,[xc,xa^-1,xf])],[4,iarel(6,[xc,xb,xf^-1])]]),
#thetaN5check(xa,xb,xc,["Mc",xb,xa,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xb,xa,xf]),[[16,theta([["M",xc,xb]],iarel(5,[xb,xa,xf]))],[7,iarel(2,[xb,xa^-1,xf,xc^-1,xa^-1,xf])],[7,iarel(3,[xb,xa^-1,xf,xc,xa])],[7,iw(iarel(5,[xb,xa,xf]))],[1,iw(iarel(5,[xc^-1,xa,xf]))]]),
#thetaN5check(xa,xb,xc,["Mc",xd,xa,xb]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xd,xa,xb]),[[1,iarel(2,[xc,xb^-1,xa^-1,xd,xa,xb])]]),
#thetaN5check(xa,xb,xc,["Mc",xa,xc,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xa,xc,xf]),[[13,iw(iarel(5,[xc,xf,xb^-1]))],[13,iarel(3,[xc,xb^-1,xf,xa,xf])],[15,iw(iarel(5,[xc,xb,xf]))],[15,iarel(2,[xc^-1,xa^-1,xf^-1,xc,xf,xb])],[18,iarel(8,[xb,xf^-1,xa^-1,xc,xf])],[21,iw(iarel(5,[xc,xf,xa^-1]))],[20,iarel(5,[xc,xb,xf])],[16,iarel(2,[xc,xa^-1,xf^-1,xb,xa^-1,xf^-1])],[17,iarel(6,[xc,xf^-1,xa^-1])],[1,iarel(5,[xb,xf^-1,xa^-1])],[19,iarel(7,[xc,xb,xa^-1,xf^-1])],[14,iarel(3,[xb,xa^-1,xf^-1,xc,xf^-1])],[12,iarel(1,[xa,xf,xc,xf])],[11,iarel(1,[xa,xf,xb,xf^-1])],[11,exiarel(2,[xb^-1,xc,xf,xa^-1,xf^-1])],[5,iarel(2,[xa,xc,xf,xb^-1,xc,xf])],[6,iarel(2,[xa^-1,xf^-1,xc,xb^-1,xc,xf])],[7,iarel(7,[xa,xb^-1,xc,xf])],[7,iarel(6,[xa^-1,xf,xc])],[5,iarel(2,[xa^-1,xf^-1,xc,xa,xc,xf])],[10,iw(iarel(5,[xa^-1,xf,xc]))],[6,iarel(2,[xa^-1,xf,xc,xa,xc,xf])]]),
#thetaN5check(xa,xb,xc,["Mc",xc,xa,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xc,xa,xf]),[[7,iw(iarel(5,[xc,xb,xa]))],[3,iarel(6,[xc^-1,xb,xa])],[2,iarel(2,[xc^-1,xb,xa,xc,xa,xf])],[4,iarel(5,[xc,xb,xa])],[4,iarel(6,[xc,xa,xb])]]),
#thetaN5check(xa,xb,xc,["Mc",xd,xa,xc]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xd,xa,xc]),[[16,theta([["M",xc,xb],["M",xb,xa]],iarel(9,[xc,xa,xd,xa]))],[5,iw(iarel(9,[xb,xa,xd,xa]))]]),
#thetaN5check(xa,xb,xc,["Mc",xb,xc,xf]),
applyrels(thetaN5check(xa,xb,xc,["Mc",xb,xc,xf]),[[12,iw(iarel(7,[xc,xb,xa,xf]))],[9,cyw(-1,iw(exiarel(2,[xb,xa,xf,xc,xa^-1])))],[9,iarel(5,[xb,xa^-1,xf])],[8,iarel(3,[xb,xa^-1,xf,xc,xf])],[8,exiarel(2,[xb,xf,xa^-1,xc,xf])],[16,iarel(6,[xc,xa,xf])],[9,iw(exiarel(1,[xb^-1,xa^-1,xc]))],[10,iw(iarel(4,[xb,xa,xc]))],[14,iw(iarel(5,[xc,xa,xf]))],[14,iarel(3,[xc,xf,xa^-1,xb,xa^-1])],[14,iw(iarel(4,[xb^-1,xa,xc]))],[18,exiarel(1,[xb^-1,xa,xc])],[10,iarel(6,[xc,xb^-1,xa])],[10,iw(iarel(5,[xc^-1,xb,xa]))],[10,iarel(2,[xc,xf,xa^-1,xc^-1,xa,xb])],[12,iarel(6,[xc^-1,xb,xa])],[14,iw(iarel(5,[xc,xb,xa]))],[2,iarel(6,[xc,xf,xb^-1])],[2,iw(iarel(5,[xc^-1,xf^-1,xb^-1]))],[1,iw(iarel(5,[xc^-1,xb,xf^-1]))],[1,iarel(2,[xc,xa^-1,xf,xc^-1,xf^-1,xb])],[3,iw(iarel(5,[xc^-1,xf,xb]))],[4,iw(iarel(5,[xc^-1,xb^-1,xf]))],[6,iarel(6,[xc,xb^-1,xf])]]),
#thetaN5check(xa,xb,xc,["Mc",xc,xb,xf]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xc,xb,xf]),[[7,iarel(6,[xc,xa,xb^-1])],[7,iw(iarel(5,[xc^-1,xa^-1,xb^-1]))],[4,iw(iarel(5,[xc^-1,xb^-1,xa^-1]))],[3,iw(iarel(5,[xc^-1,xa^-1,xb]))],[2,iarel(2,[xc^-1,xb,xa,xc,xa,xf])],[3,iw(iarel(5,[xc^-1,xb^-1,xa]))],[5,iarel(6,[xc,xb^-1,xa])]]),
#thetaN5check(xa,xb,xc,["Mc",xd,xb,xc]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xd,xb,xc]),[[8,theta([["M",xc,xb]],iw(iarel(9,[xb,xa,xd,xa])))],[14,iarel(9,[xc,xb,xd,xb])],[0,theta([["M",xb,xa]],iw(iarel(9,[xc,xb,xd,xb])))],[8,iarel(6,[xd,xb,xa])],[6,iw(iarel(5,[xd^-1,xb,xa]))],[5,iw(iarel(5,[xd^-1,xa,xb^-1]))],[4,iarel(2,[xd^-1,xb^-1,xa^-1,xd,xb,xc])],[7,iarel(5,[xd,xa^-1,xb])],[6,iarel(5,[xd,xb^-1,xa^-1])],[6,iarel(6,[xd,xa^-1,xb^-1])]]),
#thetaN5check(xa,xb,xc,["Mc",xa,xb,xc]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xa,xb,xc]),[[11,exiarel(1,[xb^-1,xa,xc])],[7,iw(iarel(5,[xc,xb,xa]))],[15,iarel(5,[xc,xa,xb^-1])],[6,iw(iarel(5,[xa^-1,xb^-1,xc^-1]))],[9,exiarel(6,[xa,xc^-1,xb^-1])],[8,iarel(6,[xa,xb^-1,xc^-1])],[10,exiarel(1,[xb^-1,xc^-1,xa^-1])],[11,exiarel(1,[xc,xb^-1,xa^-1])],[7,iw(iarel(4,[xc^-1,xa^-1,xb]))],[6,iw(iarel(4,[xb,xc^-1,xa]))],[4,iarel(1,[xb,xc^-1,xa,xc^-1])],[5,iarel(5,[xb,xc,xa^-1])],[6,iarel(4,[xb^-1,xa,xc])],[6,iarel(1,[xc,xa^-1,xb,xa^-1])],[2,exiarel(1,[xa^-1,xc,xb])],[8,iw(exiarel(1,[xc,xa^-1,xb^-1]))],[4,iarel(1,[xc,xb^-1,xa,xb^-1])],[7,cyw(2,exiarel(6,[xb^-1,xc,xa^-1]))],[4,iw(iarel(4,[xa^-1,xb^-1,xc]))],[3,iarel(4,[xc,xb,xa])]]),
#thetaN5check(xa,xb,xc,["Mc",xb,xa,xc]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xb,xa,xc]),[[3,iarel(5,[xc,xa,xb^-1])],[2,iarel(1,[xc,xa,xb,xa])],[1,iw(iarel(5,[xb^-1,xa,xc]))],[2,iw(exiarel(1,[xc,xa^-1,xb^-1]))],[4,exiarel(1,[xb^-1,xa^-1,xc])],[0,iarel(1,[xc,xa,xb,xa])]]),
#thetaN5check(xa,xb,xc,["Mc",xc,xa,xb]),
	applyrels(thetaN5check(xa,xb,xc,["Mc",xc,xa,xb]),[[2,iw(iarel(9,[xb,xa,xc,xa]))],[3,iarel(5,[xc,xb,xa])],[5,iw(exiarel(1,[xb^-1,xa,xc]))],[3,iw(iarel(5,[xc,xb,xa]))],[4,exiarel(1,[xb^-1,xa,xc])],[2,iw(iarel(9,[xb^-1,xa,xc,xa]))]])
];



#Verifying that the action of theta on the L-presentation for IA_n agrees with the conjugation action of Aut(F_n) on IA_n.

thetavsconjrel := function(by,on)
	local m1, m2;
	if by[1]="C" then
		m1 := ["M",genof(by[2]),by[3]];
		m2 := ["M",genof(by[2])^-1,by[3]];
		return pw(theta([m1,m2],[on]),[by,invertmove(on),invertmove(by)]);
	elif by[1]="Mc" then
		m1 := ["M",by[2],by[3]];
		m2 := ["M",by[2],by[4]];
		return pw(theta([invertmove(m2),invertmove(m1),m2,m1],[on]),[by,invertmove(on),invertmove(by)]);
	else return false;
	fi;
end;

thetaconjrellist:=[
#thetavsconjrel(["C",xa,xb],["C",xc,xd]),
	applyrels(thetavsconjrel(["C",xa,xb],["C",xc,xd]),[[0,iarel(1,[xa,xb,xc,xd])]]),
#thetavsconjrel(["C",xa,xb],["C",xa,xd]),
	applyrels(thetavsconjrel(["C",xa,xb],["C",xa,xd]),[[3,iarel(6,[xa^-1,xd,xb^-1])]]),
#thetavsconjrel(["C",xa,xb],["C",xc,xa]),
	applyrels(thetavsconjrel(["C",xa,xb],["C",xc,xa]),[[0,iarel(4,[xa,xb,xc])]]),
#thetavsconjrel(["C",xa,xb],["C",xb,xd]),
	applyrels(thetavsconjrel(["C",xa,xb],["C",xb,xd]),[[3,iarel(6,[xa^-1,xd^-1,xb^-1])],[1,iarel(4,[xb,xd^-1,xa])]]),
#thetavsconjrel(["C",xa,xb],["C",xc,xb]),
	applyrels(thetavsconjrel(["C",xa,xb],["C",xc,xb]),[[0,iarel(1,[xa,xb,xc,xb])]]),
thetavsconjrel(["C",xa,xb],["C",xa,xb]),
thetavsconjrel(["C",xa,xb],["C",xb,xa]),

#thetavsconjrel(["C",xa,xb],["Mc",xc,xd,xe]),
	applyrels(thetavsconjrel(["C",xa,xb],["Mc",xc,xd,xe]),[[0,iarel(3,[xc,xd,xe,xa,xb])]]),
thetavsconjrel(["C",xa,xb],["Mc",xa,xd,xe]),
#thetavsconjrel(["C",xa,xb],["Mc",xc,xa,xe]),
	applyrels(thetavsconjrel(["C",xa,xb],["Mc",xc,xa,xe]),[[9,exiarel(3,[xc,xa,xe,xb^-1])],[6,iarel(1,[xa,xb,xc,xb])],[9,iarel(1,[xc,xb,xa,xb])],[9,iarel(9,[xe,xb^-1,xc,xa])],[3,iw(iarel(5,[xc,xb,xe]))]]),
#thetavsconjrel(["C",xa,xb],["Mc",xb,xd,xe]),
	applyrels(thetavsconjrel(["C",xa,xb],["Mc",xb,xd,xe]),[[4,iarel(7,[xa,xb,xd,xe])],[4,iarel(6,[xa^-1,xe,xd])]]),
#thetavsconjrel(["C",xa,xb],["Mc",xc,xb,xe]),
	applyrels(thetavsconjrel(["C",xa,xb],["Mc",xc,xb,xe]),[[0,iarel(3,[xc,xb,xe,xa,xb])]]),
thetavsconjrel(["C",xa,xb],["Mc",xa,xb,xe]),
#thetavsconjrel(["C",xa,xb],["Mc",xb,xa,xe]),
	applyrels(thetavsconjrel(["C",xa,xb],["Mc",xb,xa,xe]),[[5,iw(iarel(6,[xa^-1,xe,xb^-1]))],[8,iarel(4,[xa^-1,xb,xe])],[5,iarel(4,[xe^-1,xb^-1,xa])],[6,iw(iarel(4,[xa^-1,xb,xe]))],[3,exiarel(1,[xa^-1,xe,xb^-1])],[6,exiarel(1,[xe,xa^-1,xb^-1])],[1,exiarel(6,[xb,xa,xe])],[4,iarel(1,[xa,xb^-1,xe,xb^-1])],[0,iarel(1,[xa,xb,xe,xb^-1])]]),
thetavsconjrel(["C",xa,xb],["Mc",xc,xa,xb]),

#thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xe]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xe]),[[1,iarel(3,[xa,xb,xc,xd,xe^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xe]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xe]),[[1,iw(exiarel(4,[xa,xc,xe,xb]))],[11,iarel(6,[xa,xc,xb])],[9,iw(iarel(5,[xa^-1,xc,xb]))],[8,iw(iarel(5,[xa^-1,xb,xc^-1]))],[8,iarel(2,[xa,xb^-1,xe,xa^-1,xc^-1,xb^-1])],[10,iarel(6,[xa^-1,xb^-1,xc^-1])],[11,iw(iarel(5,[xa,xc,xb]))],[10,iw(iarel(5,[xa,xb,xc^-1]))],[7,iw(iarel(5,[xa,xc,xe]))],[5,iw(iarel(5,[xa,xb,xe]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xa]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xa]),[[5,iarel(7,[xd,xa,xb,xc])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xe]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xe]),[[14,iw(iarel(9,[xb,xe^-1,xa,xc]))],[13,iw(iarel(5,[xa,xc^-1,xb]))],[10,cyw(-1,iarel(6,[xa^-1,xc^-1,xb]))],[6,iarel(5,[xa,xc^-1,xb])],[10,iw(iarel(5,[xa,xb,xe^-1]))],[6,iarel(6,[xa,xb,xc^-1])],[5,iarel(2,[xa,xe^-1,xb,xa^-1,xb,xc^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xb]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xb]),[[1,iarel(3,[xa,xb,xc,xd,xb^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xe]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xe]),[[6,iw(iarel(5,[xa,xc,xe^-1]))],[2,iw(exiarel(1,[xc,xe,xa]))],[1,iw(iarel(9,[xc,xe,xa,xb]))],[3,iarel(1,[xc,xe,xa,xb])],[4,exiarel(1,[xc,xe,xa])],[1,iarel(1,[xc,xe,xa,xb^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xc]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xd,xc]),[[1,iarel(3,[xa,xb,xc,xd,xc^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xb]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xb]),[[2,iw(iarel(5,[xa,xc,xb]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xa]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xa]),[[2,iw(iarel(5,[xa,xc,xb]))],[3,iarel(5,[xa,xc,xb])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xc]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xa,xc]),[[4,iarel(5,[xa,xc^-1,xb])],[4,iarel(6,[xa,xb,xc^-1])],[4,iw(iarel(5,[xa^-1,xb^-1,xc^-1]))],[4,iarel(2,[xa,xb^-1,xc,xa^-1,xc^-1,xb^-1])],[8,iarel(5,[xa,xb^-1,xc])],[7,iarel(5,[xa,xc^-1,xb^-1])],[7,iarel(6,[xa,xb^-1,xc^-1])],[5,iw(iarel(5,[xa,xb,xc]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xa]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xa]),[[3,iw(iarel(5,[xa,xb^-1,xc]))],[4,iw(iarel(5,[xa,xc^-1,xb^-1]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xc]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xb,xc]),[[4,iarel(5,[xa,xc^-1,xb])],[5,iarel(5,[xa,xc,xb^-1])],[4,iarel(5,[xa,xb,xc])],[3,iarel(1,[xb,xc^-1,xa,xc^-1])],[4,iarel(9,[xb,xc,xa,xc])],[0,iarel(1,[xa,xc,xb,xc])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xb]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["C",xc,xb]),[[3,iw(iarel(5,[xa,xb^-1,xc]))],[4,iw(iarel(5,[xa,xc^-1,xb^-1]))],[2,iw(exiarel(1,[xc,xb,xa]))]]),

#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xe,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xe,xf]),[[0,iarel(2,[xa,xb,xc,xd,xe,xf])]]),	
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xe,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xe,xf]),[[2,iw(iarel(5,[xa,xc,xb]))],[3,iarel(5,[xa,xc^-1,xb])],[2,iarel(5,[xa,xb^-1,xc^-1])],[2,iarel(6,[xa,xc^-1,xb^-1])],[1,iarel(2,[xa,xe,xf,xa^-1,xc^-1,xb^-1])],[5,iarel(5,[xa,xb^-1,xc])],[4,iarel(5,[xa,xc^-1,xb^-1])],[4,iarel(6,[xa,xb^-1,xc^-1])],[3,iarel(5,[xa,xc,xb])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xa,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xa,xf]),[[16,iarel(8,[xa,xb,xc,xd,xf])],[9,iarel(6,[xd^-1,xb,xc])],[5,iw(iarel(5,[xd,xb,xf]))],[8,iarel(2,[xd^-1,xb,xc,xd,xa,xf])],[8,iarel(5,[xd^-1,xc^-1,xb])],[6,iarel(2,[xd^-1,xc^-1,xb,xd,xc^-1,xf])],[5,iarel(2,[xd^-1,xc^-1,xb,xd,xf,xb])],[8,iw(iarel(5,[xd,xc,xf]))],[5,iw(iarel(6,[xd^-1,xc^-1,xb]))],[5,iarel(5,[xd,xc,xb])],[0,iw(exiarel(4,[xd,xb,xf,xc]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xe,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xe,xf]),[[2,iw(iarel(5,[xa,xc,xb]))],[11,iarel(5,[xa,xc,xb])],[11,cyw(-3,iarel(7,[xa,xb,xe,xf]))],[7,iw(iarel(8,[xb,xe,xf,xa,xc]))],[2,iarel(2,[xa^-1,xe,xf,xa,xc,xb])],[4,iarel(6,[xa,xf,xe])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xb,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xb,xf]),[[0,iarel(2,[xa,xb,xc,xd,xb,xf])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xe,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xe,xf]),[[4,iarel(7,[xa,xc,xe,xf])],[4,iarel(6,[xa,xf,xe])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xc,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xd,xc,xf]),[[0,iarel(2,[xa,xb,xc,xd,xc,xf])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xb,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xb,xf]),[[2,iw(iarel(5,[xa,xc,xb]))],[3,iarel(5,[xa,xc^-1,xb])],[2,iarel(5,[xa,xb^-1,xc^-1])],[2,iarel(6,[xa,xc^-1,xb^-1])],[1,iarel(2,[xa,xb,xf,xa^-1,xc^-1,xb^-1])],[5,iarel(5,[xa,xb^-1,xc])],[4,iarel(5,[xa,xc^-1,xb^-1])],[4,iarel(6,[xa,xb^-1,xc^-1])],[5,iarel(5,[xa,xc^-1,xb])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xa,xf]),
	applyrels(pw(theta([["M",xa,xc],["M",xa,xb]],[["Mc",xb,xa,xf]]),theta([["M",xa,xb]],applyrels(theta([["M",xa,xc]],[["Mc",xa,xb,xc],["Mc",xb,xf,xa],["Mc",xa,xc,xb]]),[[7,iw(iarel(5,[xa,xc,xb]))],[1,iarel(5,[xa,xc^-1,xb])]]))),[[13,iarel(5,[xa,xb,xc^-1])],[6,iarel(5,[xb^-1,xf,xc])],[6,iarel(6,[xb^-1,xc,xf])],[8,iarel(1,[xb,xc,xa,xf^-1])],[6,iw(iarel(9,[xb^-1,xc^-1,xa,xf]))],[10,iarel(2,[xb,xf,xc,xa^-1,xf,xc])],[11,iw(iarel(7,[xa,xb,xc,xf]))],[11,iarel(6,[xa,xc,xf])],[9,iarel(3,[xb,xf,xc,xa,xf])],[5,iw(exiarel(2,[xb,xc,xf,xa,xc^-1]))],[12,cyw(3,exiarel(2,[xb,xc,xf,xa,xf]))],[7,iw(iarel(5,[xa,xc,xf]))],[13,iw(iarel(5,[xa,xf^-1,xb^-1]))],[14,iw(iarel(5,[xa,xb,xf^-1]))],[10,iarel(6,[xa^-1,xb,xf^-1])],[9,iarel(2,[xa^-1,xb,xf^-1,xa,xf,xc])],[1,iw(exiarel(4,[xa,xc^-1,xf,xb^-1]))],[3,iw(iarel(5,[xa,xb,xf]))],[4,iw(iarel(5,[xa,xf^-1,xb]))],[6,iarel(6,[xa^-1,xf^-1,xb])],[1,iw(iarel(5,[xa,xb,xc^-1]))],[2,iarel(2,[xa^-1,xc,xf,xb,xc,xf])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xc,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xc,xf]),[[2,iw(iarel(5,[xa,xc,xb]))],[3,iarel(5,[xa,xc^-1,xb])],[2,iarel(5,[xa,xb^-1,xc^-1])],[2,iarel(6,[xa,xc^-1,xb^-1])],[1,iarel(2,[xa,xc,xf,xa^-1,xc^-1,xb^-1])],[5,iarel(5,[xa,xb^-1,xc])],[4,iarel(5,[xa,xc^-1,xb^-1])],[4,iarel(6,[xa,xb^-1,xc^-1])],[3,iarel(5,[xa,xc,xb])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xa,xf]),
	applyrels(pw(theta([["M",xa,xc],["M",xa,xb]],[["Mc",xc,xa,xf]]),theta([["M",xa,xb]],applyrels(theta([["M",xa,xc]],[["Mc",xa,xb,xc],["Mc",xc,xf,xa],["Mc",xa,xc,xb]]),[[3,iarel(5,[xa,xc,xb])],[5,iw(iarel(5,[xa,xc,xb]))]]))),[[15,iarel(5,[xa,xb,xc^-1])],[5,iarel(1,[xa,xf,xc,xb^-1])],[6,cyw(3,iarel(9,[xc^-1,xb^-1,xa,xf]))],[11,cyw(1,iarel(6,[xc,xb,xf^-1]))],[8,iarel(5,[xc,xf,xb])],[13,iw(iarel(5,[xa,xb,xc^-1]))],[2,iarel(7,[xa,xc,xb,xf])],[2,iarel(6,[xa^-1,xf,xb])],[3,iarel(3,[xc,xb,xf,xa,xf])],[4,iw(exiarel(2,[xc,xb,xf,xa,xf]))],[14,exiarel(2,[xc,xb,xf,xa,xb^-1])],[4,iarel(5,[xa,xf^-1,xc^-1])],[3,iarel(5,[xa,xc,xf^-1])],[3,iarel(6,[xa,xf^-1,xc])],[1,iarel(2,[xa^-1,xf^-1,xc,xa,xf,xb])],[6,iarel(5,[xa,xb,xf])],[5,iw(exiarel(4,[xa,xb^-1,xc^-1,xf]))],[4,iarel(5,[xa,xc,xf])],[3,iarel(5,[xa,xf^-1,xc])],[3,iarel(6,[xa,xc,xf^-1])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xc,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xc,xf]),[[13,iarel(5,[xa,xc,xb])],[9,iw(iarel(8,[xb,xc,xf,xa,xc]))],[8,iarel(7,[xa,xb,xc,xf])],[8,iarel(6,[xa,xf,xc])],[4,iarel(2,[xa^-1,xc,xf,xa,xc,xb])],[2,iw(iarel(5,[xa,xc,xb]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xb,xf]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xb,xf]),[[4,iarel(7,[xa,xc,xb,xf])],[4,iarel(6,[xa,xf,xb])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xb,xc]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xa,xb,xc]),[[2,iw(iarel(5,[xa,xc,xb]))],[13,iarel(5,[xa,xc,xb])],[4,iarel(6,[xa,xc,xb])],[2,iw(iarel(5,[xa^-1,xc,xb]))],[1,iw(iarel(5,[xa^-1,xb,xc^-1]))],[1,iarel(2,[xa,xb,xc,xa^-1,xc^-1,xb^-1])],[3,iw(iarel(5,[xa^-1,xc,xb^-1]))],[4,iw(iarel(5,[xa^-1,xb,xc]))],[6,iarel(6,[xa,xb,xc])]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xa,xc]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xb,xa,xc]),[[19,iarel(1,[xb,xc,xa,xc])],[19,iw(iarel(5,[xb,xc,xa]))],[15,iarel(1,[xb,xc^-1,xa,xc])],[5,iarel(6,[xa,xc,xb])],[3,iw(iarel(5,[xa^-1,xc,xb]))],[6,iw(iarel(5,[xa,xb,xc]))],[2,iarel(2,[xa^-1,xb,xc^-1,xa,xb,xc])],[3,iarel(6,[xa^-1,xc^-1,xb])],[3,iw(iarel(5,[xa,xc,xb]))],[1,iw(iarel(5,[xa,xc,xb]))]]),
#thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xa,xb]),
	applyrels(thetavsconjrel(["Mc",xa,xb,xc],["Mc",xc,xa,xb]),[[19,iarel(5,[xa,xc,xb])],[2,iw(iarel(5,[xa,xc,xb]))],[10,exiarel(1,[xc,xb^-1,xa])],[8,iarel(1,[xa,xb^-1,xc,xb^-1])],[9,iarel(1,[xa,xb^-1,xc,xb^-1])],[13,iarel(9,[xc,xb^-1,xa,xb^-1])],[7,iarel(5,[xa,xb^-1,xc])],[5,iw(iarel(5,[xa,xc,xb]))]])
];



# Verifying that the relations for the Birman exact sequence kernel, follow from the relations of the presentation for IA_n

kfromialist:=
[
#krel 1--3 are the same as iarel 1--3
#krel 4:
applyrels(krel(4,[xa,y,xb]),[[3,iarel(9,[y,xb^-1,xa,xb])],[3,iarel(5,[xa,xb^-1,y])]]),
#krel 5:
applyrels(krel(5,[xa,y,xb]),[[0,iw(iarel(9,[xb,y^-1,xa,y]))],[2,iw(iarel(5,[xa,y^-1,xb]))]]),
#krel 6 is the same as iarel 5
#krel 7:
applyrels(krel(7,[xa,y,xb]),[[6,iarel(4,[y^-1,xb,xa])],[0,iw(iarel(6,[xa,y,xb]))]]),
#krel 8:
applyrels(krel(8,[xa,y,xb,xc]),[[3,iarel(8,[xb,y^-1,xc,xa,y])],[2,iw(iarel(5,[xa,y^-1,xc]))]]),
#krel 9:
applyrels(krel(9,[xa,y,xb,xc]),[[4,iarel(9,[y,xc,xa,xb])],[10,iw(iarel(9,[y,xc,xa,xb]))],[5,iarel(3,[xa,xc,y,xb,y])],[4,cyw(-1,iw(iarel(9,[xb,y^-1,xa,y])))],[7,iw(iarel(5,[xa,y^-1,xb]))],[0,iw(iarel(4,[xb^-1,y^-1,xa]))],[7,iarel(4,[xb^-1,y^-1,xa])],[4,iarel(3,[xa,y,xc,xb,y])],[8,cyw(1,iarel(6,[xa^-1,y^-1,xb]))],[7,iarel(5,[xa^-1,xb,y^-1])],[3,iarel(2,[xa^-1,xb^-1,y^-1,xa,y,xc])],[4,iw(iarel(5,[xa^-1,xb,y^-1]))],[0,iarel(6,[xa,xb,y^-1])]]),
#krel 10:
applyrels(krel(10,[xa,y,xb,xc]),[[10,iarel(9,[y^-1,xc,xa,xb])],[4,iarel(9,[y,xc,xa,xb])],[7,iarel(9,[xc,y^-1,xa,y])],[9,iarel(5,[xa,y^-1,xc])],[4,iarel(3,[xa,y,xb,xc,y])],[0,iarel(1,[xa,xb^-1,xc,y^-1])],[3,iarel(1,[xc,y,xa,xb])],[1,iw(iarel(9,[xc,y^-1,xa,y]))],[3,iw(iarel(5,[xa,y^-1,xc]))]])
];

# Verifying that the action by phi agrees with the action by theta in where applicable

thetavsphi:=function(by,on)
	return pw(theta([by],[on]),phi([by],iw([on])));
end;


thetavsphilist:=
[
thetavsphi(["M",xa,y],["C",xb,y]),  
thetavsphi(["M",xa,y],["C",xa,y]),  
thetavsphi(["M",xa,y],["C",y,xb]),  
thetavsphi(["M",xa,y],["C",y,xa]),  
thetavsphi(["M",xa,y],["Mc",xb,y,xc]),  
thetavsphi(["M",xa,y],["Mc",xa,y,xb]),  
thetavsphi(["M",xa,y],["Mc",xb,y,xa]),  

thetavsphi(["M",xa,y^-1],["C",xb,y]),  
thetavsphi(["M",xa,y^-1],["C",xa,y]),  
thetavsphi(["M",xa,y^-1],["C",y,xb]),  
thetavsphi(["M",xa,y^-1],["C",y,xa]),  
thetavsphi(["M",xa,y^-1],["Mc",xb,y,xc]),  
thetavsphi(["M",xa,y^-1],["Mc",xa,y,xb]),  
#thetavsphi(["M",xa,y^-1],["Mc",xb,y,xa]),  
	applyrels(thetavsphi(["M",xa,y^-1],["Mc",xb,y,xa]),[[1,iw(exiarel(1,[xa,y,xb]))]]),


thetavsphi(["M",xa,xb],["C",xc,y]),  
thetavsphi(["M",xa,xb],["C",xa,y]),  
thetavsphi(["M",xa,xb],["C",xb,y]),  
thetavsphi(["M",xa,xb],["C",y,xc]),  
thetavsphi(["M",xa,xb],["C",y,xa]),  
thetavsphi(["M",xa,xb],["C",y,xb]),  
thetavsphi(["M",xa,xb],["Mc",xc,y,xd]),  
#thetavsphi(["M",xa,xb],["Mc",xa,y,xc]),
	applyrels(thetavsphi(["M",xa,xb],["Mc",xa,y,xc]),[[5,iw(iarel(9,[y,xc,xa,xb^-1]))]]),
#thetavsphi(["M",xa,xb],["Mc",xc,y,xa]),
	applyrels(thetavsphi(["M",xa,xb],["Mc",xc,y,xa]),[[5,iw(iarel(9,[y,xa,xc,xb]))]]),
#thetavsphi(["M",xa,xb],["Mc",xb,y,xc]),
	applyrels(thetavsphi(["M",xa,xb],["Mc",xb,y,xc]),[[7,iarel(9,[y,xc,xa,xb^-1])],[1,iarel(2,[xb,y,xc,xa^-1,y,xc])],[4,iarel(6,[xa,xc,y])],[2,iw(iarel(7,[xa,xb,xc,y]))]]),
thetavsphi(["M",xa,xb],["Mc",xc,y,xb]), 
#thetavsphi(["M",xa,xb],["Mc",xa,y,xb]),
	applyrels(thetavsphi(["M",xa,xb],["Mc",xa,y,xb]),[[3,iarel(5,[xa,xb,y])]]),
thetavsphi(["M",xa,xb],["Mc",xb,y,xa]),

thetavsphi(["M",xa,xb^-1],["C",xc,y]),  
thetavsphi(["M",xa,xb^-1],["C",xa,y]),  
thetavsphi(["M",xa,xb^-1],["C",xb,y]),  
thetavsphi(["M",xa,xb^-1],["C",y,xc]),  
thetavsphi(["M",xa,xb^-1],["C",y,xa]),  
thetavsphi(["M",xa,xb^-1],["C",y,xb]),  
thetavsphi(["M",xa,xb^-1],["Mc",xc,y,xd]),  
#thetavsphi(["M",xa,xb^-1],["Mc",xa,y,xc]),
	applyrels(thetavsphi(["M",xa,xb^-1],["Mc",xa,y,xc]),[[5,iw(iarel(9,[y,xc,xa,xb]))]]),
#thetavsphi(["M",xa,xb^-1],["Mc",xc,y,xa]),
	applyrels(thetavsphi(["M",xa,xb^-1],["Mc",xc,y,xa]),[[5,iw(iarel(9,[y,xa,xc,xb^-1]))]]),
#thetavsphi(["M",xa,xb^-1],["Mc",xb,y,xc]),
	applyrels(thetavsphi(["M",xa,xb^-1],["Mc",xb,y,xc]),[[0,iarel(2,[xb,y,xc,xa,y,xc])]]),
thetavsphi(["M",xa,xb^-1],["Mc",xc,y,xb]), 
#thetavsphi(["M",xa,xb^-1],["Mc",xa,y,xb]),
	applyrels(thetavsphi(["M",xa,xb^-1],["Mc",xa,y,xb]),[[3,iw(iarel(9,[y,xb,xa,xb]))]]),
thetavsphi(["M",xa,xb^-1],["Mc",xb,y,xa]),  
];



rewritethetaR5R6:=
[
# ["M",xd,xe] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xd,xe]],iarel(5,[xa,xb,xc])),[[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xa,xd] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xa^-1,xd]
# ["M",xa^-1,xd] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xa^-1,xd]],iarel(5,[xa,xb,xc])),[[1,iarel(2,[xa,xb,xc,xa^-1,xd^-1,xb])],[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xb,xd] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xb,xd]],iarel(5,[xa,xb,xc])),[[5,iw(iarel(5,[xa,xb^-1,xc]))],[1,iw(iarel(5,[xa,xd,xc]))]]),
# ["M",xb^-1,xd] on iarel(5,[xa,xb,xc])  # invert 2nd parameter, follows from ["M",xb,xd]
# ["M",xc,xd] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xc,xd]],iarel(5,[xa,xb,xc])),[[4,iarel(5,[xa,xd^-1,xb])],[4,iarel(6,[xa,xb,xd^-1])],[2,iarel(2,[xa^-1,xb,xd^-1,xa,xb,xc])],[4,iw(iarel(5,[xa,xb^-1,xc]))],[3,iw(iarel(5,[xa^-1,xb^-1,xd^-1]))],[4,iw(iarel(5,[xa^-1,xd,xb^-1]))],[0,iarel(6,[xa,xd,xb^-1])]]),
# ["M",xc^-1,xd] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xc,xd]
# ["M",xd,xa] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xd,xa^-1]
# ["M",xd,xa^-1] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xd,xa^-1]],iarel(5,[xa,xb,xc])),[[5,cyw(1,iarel(8,[xa,xb,xc,xd,xb^-1]))],[6,iarel(3,[xd,xb^-1,xc,xa,xb])],[4,iarel(2,[xd,xb^-1,xc,xa,xb,xc])],[8,iw(iarel(5,[xa,xb,xc]))],[5,iw(iarel(5,[xd,xb,xc]))]]),
# ["M",xd,xb] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xd,xb]],iarel(5,[xa,xb,xc])),[[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xd,xb^-1] on iarel(5,[xa,xb,xc]) # invert 2nd parameter, follows from ["M",xd,xb]
# ["M",xd,xc] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xd,xc]],iarel(5,[xa,xb,xc])),[[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xd,xc^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xd,xc]
# ["M",xa,xb] on iarel(5,[xa,xb,xc])
		applyrels(theta([["M",xa,xb]],iarel(5,[xa,xb,xc])),[[1,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xa^-1,xb] on iarel(5,[xa,xb,xc]) # invert 2nd parameter and conjugation relation, follows from ["M",xa,xb]
# ["M",xa,xb^-1] on iarel(5,[xa,xb,xc]) # invert 2nd parameter, follows from ["M",xa,xb] 
# ["M",xa^-1,xb^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xa,xb]
# ["M",xb,xa] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xb,xa]],iarel(5,[xa,xb,xc])),[[6,iw(iarel(5,[xa^-1,xb^-1,xc^-1]))],[6,iw(iarel(6,[xa^-1,xc^-1,xb^-1]))],[7,iarel(1,[xc,xa^-1,xb,xa^-1])],[6,cyw(-2,iw(exiarel(6,[xa,xb^-1,xc^-1])))],[11,iw(exiarel(1,[xc^-1,xb^-1,xa^-1]))],[10,iarel(1,[xa,xc,xb,xc])],[11,iw(iarel(5,[xb,xc,xa^-1]))],[6,cyw(1,iarel(4,[xc^-1,xa,xb]))],[10,cyw(1,iarel(4,[xb,xa^-1,xc]))],[4,theta([["M",xb^-1,xc^-1]],iarel(1,[xc,xb^-1,xa,xb^-1]))],[5,iarel(5,[xb,xc,xa^-1])],[3,iarel(1,[xa,xb^-1,xc,xb^-1])],[1,cyw(-1,iw(exiarel(6,[xb,xc^-1,xa^-1])))],[5,iw(exiarel(1,[xa^-1,xc^-1,xb^-1]))],[4,iw(exiarel(1,[xc,xa^-1,xb^-1]))],[3,iw(exiarel(1,[xa,xc,xb^-1]))],[7,iarel(4,[xa,xc^-1,xb])],[4,iarel(6,[xb^-1,xa,xc^-1])],[6,iw(iarel(5,[xb,xa,xc^-1]))],[2,iarel(1,[xb,xa^-1,xc,xa^-1])],[0,iw(iarel(4,[xb^-1,xa,xc]))]]),
# ["M",xb^-1,xa] on iarel(5,[xa,xb,xc]) # invert 2nd parameter, follows from ["M",xb,xa]
# ["M",xb,xa^-1] on iarel(5,[xa,xb,xc]) # invert 2nd parameter and conjugation relation, follows from ["M",xb,xa]
# ["M",xb^-1,xa^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xb,xa]
# ["M",xa,xc] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xa,xc]],iarel(5,[xa,xb,xc])),[[3,iarel(5,[xa,xc^-1,xb])],[3,iarel(5,[xa,xb,xc^-1])],[0,iarel(5,[xa,xc,xb^-1])]]),
# ["M",xa^-1,xc] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xa^-1,xc]],iarel(5,[xa,xb,xc])),[[1,iarel(2,[xa,xb,xc,xa^-1,xc^-1,xb])],[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xa,xc^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xa^-1,xc]
# ["M",xa^-1,xc^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xa,xc]
# ["M",xc,xa] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xc,xa]],iarel(5,[xa,xb,xc])),[[7,iw(iarel(5,[xc,xb,xa^-1]))],[3,iarel(1,[xc,xb^-1,xa,xb])],[2,exiarel(1,[xc,xb,xa^-1])],[2,iarel(1,[xa,xb^-1,xc,xb^-1])],[5,iw(iarel(5,[xc,xb,xa^-1]))],[2,iw(exiarel(1,[xa^-1,xb,xc]))]]),
# ["M",xc^-1,xa] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xc^-1,xa]],iarel(5,[xa,xb,xc])),[[2,theta([["M",xc^-1,xa]],iarel(2,[xa^-1,xc,xb,xa,xb,xc]))],[2,iw(exiarel(1,[xa^-1,xb,xc^-1]))],[8,iw(exiarel(1,[xc^-1,xb,xa^-1]))],[11,iw(exiarel(1,[xb,xc^-1,xa^-1]))],[10,exiarel(1,[xa^-1,xb^-1,xc^-1])],[7,iarel(9,[xa^-1,xb,xc^-1,xb])],[7,iarel(5,[xc^-1,xb^-1,xa^-1])],[11,exiarel(1,[xb,xc^-1,xa^-1])],[4,iarel(1,[xa,xb^-1,xc,xb])],[3,iarel(1,[xa,xb^-1,xc,xb])]]),
# ["M",xc,xa^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xc^-1,xa]
# ["M",xc^-1,xa^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xc,xa]
# ["M",xb,xc] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xb,xc]],iarel(5,[xa,xb,xc])),[[5,iarel(9,[xb,xc,xa,xc])],[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xb^-1,xc] on iarel(5,[xa,xb,xc]) # invert 2nd parameter, follows from ["M",xb,xc]
# ["M",xb,xc^-1] on iarel(5,[xa,xb,xc]) # conjugation relation and invert 2nd parameter, follows from ["M",xb,xc]
# ["M",xb^-1,xc^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xb,xc]
# ["M",xc,xb] on iarel(5,[xa,xb,xc])
	applyrels(theta([["M",xc,xb]],iarel(5,[xa,xb,xc])),[[1,iw(iarel(9,[xc,xb,xa,xb]))]]),
# ["M",xc^-1,xb] on iarel(5,[xa,xb,xc])	# invert 2nd parameter and conjugation relation, follows from ["M",xc,xb]
# ["M",xc,xb^-1] on iarel(5,[xa,xb,xc]) # invert 2nd parameter, follows from ["M",xc,xb]
# ["M",xc^-1,xb^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xc,xb]

# ["M",xd,xe] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xd,xe]],iarel(6,[xa,xb,xc])),[[0,iw(iarel(6,[xa,xb,xc]))]]),
# ["M",xa,xd] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xa,xd]],iarel(6,[xa,xb,xc])),[[3,iarel(2,[xa,xb,xd^-1,xa^-1,xb,xc])],[5,iw(iarel(5,[xa^-1,xb^-1,xc]))],[5,iarel(2,[xa,xc,xd^-1,xa^-1,xc,xb^-1])],[7,iarel(6,[xa^-1,xb^-1,xc])],[7,iw(iarel(5,[xa,xb,xc]))],[0,exiarel(4,[xa,xc,xd^-1,xb])]]),
# ["M",xa^-1,xd] on iarel(6,[xa,xb,xc]) # invert 1st parameter, follows from ["M",xa,xd]
# ["M",xd,xa] on iarel(6,[xa,xb,xc])
		applyrels(theta([["M",xd,xa]],iarel(6,[xa,xb,xc])),[[4,cyw(-2,iarel(7,[xd^-1,xa,xb,xc]))],[2,iarel(6,[xd^-1,xc,xb])],[3,iarel(2,[xd,xb,xc,xa,xb,xc])],[6,iarel(6,[xa^-1,xc,xb])],[8,exiarel(1,[xa^-1,xb,xd])],[6,cyw(3,iarel(9,[xa^-1,xc,xd,xb]))],[14,exiarel(1,[xa^-1,xc^-1,xd])],[5,iarel(1,[xd,xb^-1,xa,xb^-1])],[7,cyw(2,iarel(9,[xa^-1,xb^-1,xd,xc]))],[11,iarel(1,[xd,xb,xa,xb^-1])],[12,iw(exiarel(1,[xa^-1,xb,xd]))],[5,iarel(3,[xd,xc,xb,xa,xc])],[4,iarel(4,[xa,xc,xd])],[3,iarel(3,[xd,xb,xc,xa,xc])],[3,iw(iarel(5,[xd,xc^-1,xb]))],[2,iarel(4,[xa^-1,xc,xd])],[16,iw(exiarel(1,[xa^-1,xc,xd]))],[6,iarel(5,[xd,xc^-1,xb])],[6,iarel(6,[xd,xb,xc^-1])],[7,iarel(5,[xd,xb,xa^-1])],[5,iarel(2,[xd,xb,xa^-1,xd^-1,xb,xc^-1])],[7,iarel(6,[xd^-1,xc^-1,xb])],[1,iarel(6,[xd,xa^-1,xc])],[3,iw(iarel(5,[xd^-1,xa,xc]))],[5,iarel(5,[xd,xc,xb])],[3,iarel(2,[xd,xc,xb,xd^-1,xc,xa])],[5,iarel(6,[xd^-1,xa,xc])],[5,iw(iarel(5,[xd,xa^-1,xc]))],[9,iw(iarel(5,[xd,xc,xb]))],[13,iw(iarel(5,[xd,xb,xa^-1]))],[2,exiarel(4,[xd,xb,xa^-1,xc])]]),
# ["M",xd,xa^-1] on iarel(6,[xa,xb,xc]) # invert 1st parameter, follows from ["M",xd,xa]
# ["M",xb,xd] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xb,xd]],iarel(6,[xa,xb,xc])),[[1,theta([["M",xa,xd^-1]],iarel(2,[xa^-1,xd,xc,xa,xb,xc]))],[5,iarel(6,[xa^-1,xc,xb])],[2,iarel(6,[xa^-1,xc,xd])]]),
# ["M",xb^-1,xd] on iarel(6,[xa,xb,xc]) # conjugation relation, follows from ["M",xb,xd]
# ["M",xd,xb] on iarel(6,[xa,xb,xc]) 
	applyrels(theta([["M",xd,xb]],iarel(5,[xa,xb,xc])),[[0,iw(iarel(5,[xa,xb,xc]))]]),
# ["M",xd,xb^-1] on iarel(6,[xa,xb,xc]) # conjugation relation, follows from ["M",xd,xb]
# ["M",xc,xd] on iarel(6,[xa,xb,xc])   # no expressions with parameters of "M" involving xc and not xb are necessary to check since swapping 2nd and 3rd parameters in iarel(6) is okay
# ["M",xa,xb] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xa,xb]],iarel(6,[xa,xb,xc])),[[0,iw(iarel(5,[xa,xb,xc]))],[3,iarel(5,[xa,xb,xc])],[3,iarel(6,[xa,xc,xb])]]),
# ["M",xa^-1,xb] on iarel(6,[xa,xb,xc]) # invert 1st parameter, follows from ["M",xa,xb]
# ["M",xa,xb^-1] on iarel(6,[xa,xb,xc]) # conjugation relation and invert 1st input, follows from ["M",xa,xb]
# ["M",xa^-1,xb^-1] on iarel(5,[xa,xb,xc]) # conjugation relation, follows from ["M",xa,xb]
# ["M",xb,xa] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xb,xa]],iarel(6,[xa,xb,xc])),[[10,exiarel(1,[xa^-1,xc,xb])],[11,exiarel(1,[xc^-1,xa^-1,xb])],[14,iarel(5,[xb,xa,xc^-1])],[11,iarel(1,[xa,xb^-1,xc,xb^-1])],[10,cyw(-2,iw(exiarel(6,[xb,xc^-1,xa])))],[18,iarel(6,[xb,xc^-1,xa])],[1,iarel(5,[xb,xc^-1,xa^-1])],[4,iw(exiarel(1,[xb,xc,xa^-1]))],[7,iw(exiarel(1,[xc,xb,xa^-1]))],[1,iarel(1,[xa,xc^-1,xb,xc])],[7,iarel(4,[xa,xb,xc])],[6,iw(iarel(4,[xc^-1,xb^-1,xa]))],[5,iarel(4,[xa^-1,xb,xc])],[2,iarel(1,[xa,xb^-1,xc,xb])],[4,iarel(4,[xa^-1,xc^-1,xb])]]),
# ["M",xb^-1,xa] on iarel(6,[xa,xb,xc]) # invert 1st parameter and conjugation relation, follows from ["M",xb,xa]
# ["M",xb,xa^-1] on iarel(6,[xa,xb,xc]) # invert 1st parameter, follows from ["M",xb,xa]
# ["M",xb^-1,xa^-1] on iarel(6,[xa,xb,xc]) # conjugation relation, follows from ["M",xb,xa]
# ["M",xb,xc] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xb,xc]],iarel(6,[xa,xb,xc])),[[4,iarel(4,[xb^-1,xc,xa])],[4,iarel(1,[xa,xc^-1,xb,xc^-1])],[6,iarel(4,[xb,xc,xa])],[6,iarel(1,[xa,xc,xb,xc^-1])],[3,iarel(6,[xa^-1,xc,xb])]]),
# ["M",xb^-1,xc] on iarel(6,[xa,xb,xc])
	applyrels(theta([["M",xb^-1,xc]],iarel(6,[xa,xb,xc])),[[2,iarel(6,[xa^-1,xc,xb])]]),
# ["M",xb,xc^-1] on iarel(6,[xa,xb,xc]) # conjugation relation, follows from ["M",xb^-1,xc]
# ["M",xb^-1,xc^-1] on iarel(6,[xa,xb,xc]) # conjugation relation, follows from ["M",xb,xc]
# ["M",xc,xb] on iarel(6,[xa,xb,xc]) # etc follow from last 4 lines by swapping 2nd and 3rd parameter
];

kernellist:=[

#in terminology of the proof, iarel(5,[xa,xb,xc]) is r_1, iarel(5,[xa,xc^-1,xb]) is -r_3, iarel(5,[xa,xc^-1,xb^-1]) is -r_5 and iarel(5,[xa,xb^-1,xc^-1]) is r_7 
applyrels(iarel(5,[xa,xb,xc]),[[1,iarel(5,[xa,xc^-1,xb])],[5,iarel(5,[xa,xc^-1,xb^-1])],[2,iarel(5,[xa,xb^-1,xc^-1])],[4,iarel(6,[xa,xc^-1,xb^-1])],[3,iarel(2,[xa,xc^-1,xb^-1,xa^-1,xc^-1,xb^-1])],[3,iw(iarel(6,[xa,xc^-1,xb^-1]))]]),

# iarel(5,[xa,xb,xc]) is r_1, iarel(6,[xa,xc,xb]) is -r_{13}, iarel(6,[xa,xc,xb^-1]) is -r_{14}, iarel(5,[xa^-1,xb,xc]) is r_2
applyrels(iarel(5,[xa,xb,xc]),[[2,iarel(6,[xa,xc,xb])],[6,iarel(6,[xa,xc,xb^-1])],[5,iarel(5,[xa^-1,xb,xc])],[2,iarel(6,[xa^-1,xb,xc])],[1,iarel(2,[xa^-1,xb,xc,xa,xb,xc])],[1,iw(iarel(6,[xa^-1,xb,xc]))]]),

# iarel(5,[xa,xb,xc]) is r_1, iarel(5,[xa,xc^-1,xb^-1]) is -r_5, iarel(6,[xa,xc,xb]) is -r_{13}, iarel(6,[xa,xb^-1,xc^-1]) is r_{12}, iarel(5,[xa^-1,xb^-1,xc]) is r_2, and iarel(5,[xa^-1,xc,xb^-1]) is -r_6, 
applyrels(iarel(5,[xa,xb,xc]),[[3,iarel(5,[xa,xc^-1,xb^-1])],[2,iarel(6,[xa,xc,xb])],[5,iarel(6,[xa,xb^-1,xc^-1])],[1,iarel(5,[xa^-1,xb^-1,xc])],[4,iarel(5,[xa^-1,xc,xb^-1])],[1,iarel(6,[xa^-1,xc,xb^-1])],[0,iarel(2,[xa^-1,xc,xb^-1,xa,xc,xb^-1])],[0,iw(iarel(6,[xa^-1,xc,xb^-1]))]])
];



lemma7pt2:=[
# can invert second parameter in h6 (almost)
applyrels(iarel(8,[xa,xe,xc,xd,xe]),[[1,iw(iarel(5,[xa,xe^-1,xc]))],[4,iarel(5,[xa,xe^-1,xc])],[5,iarel(9,[xa,xe,xd,xe])],[1,iarel(3,[xa,xc,xe^-1,xd,xe^-1])],[6,iw(iarel(3,[xa,xc,xe^-1,xd,xe^-1]))],[2,iw(iarel(8,[xa,xc,xe^-1,xd,xe]))],[4,iw(iarel(5,[xd,xe,xc]))],[4,iarel(5,[xd,xe,xc])],[0,iarel(1,[xd,xe^-1,xa,xe^-1])],[2,iarel(3,[xd,xc,xe,xa,xe])],[6,iw(iarel(3,[xd,xc,xe,xa,xe]))],[6,iw(iarel(1,[xd,xe^-1,xa,xe^-1]))],[5,iarel(9,[xa,xe^-1,xd,xe])],[3,iarel(5,[xd,xe,xa])],[3,iw(iarel(5,[xd,xe,xa]))]]),

#can reorder second & third parameter in h6
applyrels(iarel(8,[xa,xb,xc,xd,xe]),[[8,iarel(3,[xa,xb,xc,xd,xe^-1])],[2,iarel(2,[xd,xc,xb,xa,xc,xb])],[8,iw(iarel(2,[xd,xc,xb,xa,xc,xb]))],[5,iw(iarel(3,[xa,xb,xc,xd,xe^-1]))],[6,iarel(8,[xa,xc,xb,xd,xe])]]),
applyrels(iarel(8,[xa,xb,xc,xd,xb]),[[8,iarel(3,[xa,xb,xc,xd,xb^-1])],[2,iarel(2,[xd,xc,xb,xa,xc,xb])],[8,iw(iarel(2,[xd,xc,xb,xa,xc,xb]))],[5,iw(iarel(3,[xa,xb,xc,xd,xb^-1]))],[6,iarel(8,[xa,xc,xb,xd,xb])]]),
applyrels(iarel(8,[xa,xb,xc,xd,xb^-1]),[[8,iarel(3,[xa,xb,xc,xd,xb])],[2,iarel(2,[xd,xc,xb,xa,xc,xb])],[8,iw(iarel(2,[xd,xc,xb,xa,xc,xb]))],[5,iw(iarel(3,[xa,xb,xc,xd,xb]))],[6,iarel(8,[xa,xc,xb,xd,xb^-1])]])
];
lemma7pt3:=[
#Equation 14:
applyrels(theta([["M",xb,xe]],iarel(1,[xa,xb,xc,xd])),[[1,iarel(1,[xc,xd,xa,xe])],[0,iw(iarel(1,[xa,xb,xc,xd]))]]),

#Equation 15:
applyrels(theta([["M",xb,xe]],iarel(1,[xa,xe,xc,xd])),[[0,iw(iarel(1,[xa,xe,xc,xd]))]]),

#Equation 16:
applyrels(theta([["M",xb,xd]],iarel(1,[xa,xb,xc,xd])),[[1,iw(iarel(1,[xa,xd,xc,xd]))],[0,iw(iarel(1,[xa,xb,xc,xd]))]]),

#Equation 17 (two computations):
applyrels(theta([["M",xa,xe^-1]],iarel(1,[xa,xb,xc,xd])),[[1,iarel(3,[xa,xe,xb,xc,xd])],[0,iw(iarel(1,[xa,xb,xc,xd]))]]),

applyrels(theta([["M",xa,xd^-1]],iarel(1,[xa,xb,xc,xd])),[[1,iarel(3,[xa,xd,xb,xc,xd])],[0,iw(iarel(1,[xa,xb,xc,xd]))]]),

#Equation 18 (six computations):
applyrels(theta([["M",xd,xe^-1]],iarel(3,[xa,xb,xc,xd,xf])),[[6,iw(iarel(3,[xa,xb,xc,xd,xf]))],[1,iarel(2,[xa,xb,xc,xd,xe,xf])]]),

applyrels(theta([["M",xd,xe^-1]],iarel(3,[xa,xb,xc,xd,xb])),[[6,iw(iarel(3,[xa,xb,xc,xd,xb]))],[1,iarel(2,[xa,xb,xc,xd,xe,xb])]]),

applyrels(theta([["M",xd,xe^-1]],iarel(3,[xa,xb,xc,xd,xb^-1])),[[4,iarel(5,[xd,xb^-1,xe])],[1,iw(iarel(5,[xd,xb^-1,xe]))],[6,iw(iarel(3,[xa,xb,xc,xd,xb^-1]))],[1,iarel(2,[xa,xb,xc,xd,xe,xb^-1])]]),

applyrels(theta([["M",xd,xb^-1]],iarel(3,[xa,xb,xc,xd,xc])),[[6,iw(iarel(3,[xa,xb,xc,xd,xc]))],[1,iarel(2,[xa,xb,xc,xd,xb,xc])]]),

applyrels(theta([["M",xd,xb]],iarel(3,[xa,xb,xc,xd,xc])),[[6,iw(iarel(3,[xa,xb,xc,xd,xc]))],[1,iarel(2,[xa,xb,xc,xd,xb^-1,xc])]]),

applyrels(theta([["M",xd,xb]],iarel(3,[xa,xb,xc,xd,xc^-1])),[[4,iarel(5,[xd,xc^-1,xb^-1])],[1,iw(iarel(5,[xd,xc^-1,xb^-1]))],[6,iw(iarel(3,[xa,xb,xc,xd,xc^-1]))],[1,iarel(2,[xa,xb,xc,xd,xb^-1,xc^-1])]]),

#Equation 19 (six computations):
applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xf,xe])),[[0,iw(iarel(2,[xa,xb,xc,xd^-1,xf,xe]))],[4,iarel(2,[xa,xb,xc,xa^-1,xe,xf])]]),  

applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xb,xe])),[[4,iarel(2,[xa,xb,xc,xa^-1,xe,xb])],[1,iarel(2,[xd^-1,xb,xe,xa^-1,xb,xe])],[0,iw(iarel(2,[xa,xb,xc,xd^-1,xb,xe]))],[0,iw(iarel(2,[xd^-1,xb,xe,xa^-1,xb,xe]))]]), 

applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xb^-1,xe])),[[4,iarel(2,[xa,xb,xc,xa^-1,xe,xb^-1])],[1,iarel(2,[xd^-1,xb^-1,xe,xa^-1,xb^-1,xe])],[0,iw(iarel(2,[xa,xb,xc,xd^-1,xb^-1,xe]))],[0,iw(iarel(2,[xd^-1,xb^-1,xe,xa^-1,xb^-1,xe]))]]),

applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xc,xb])),[[0,iw(iarel(2,[xa,xb,xc,xd^-1,xc,xb]))],[4,iarel(2,[xa,xb,xc,xa^-1,xb,xc])]]),

applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xc,xb^-1])),[[0,iw(iarel(2,[xa,xb,xc,xd^-1,xc,xb^-1]))],[4,iarel(2,[xa,xb,xc,xa^-1,xb^-1,xc])]]),

applyrels(theta([["M",xa^-1,xd]],iarel(2,[xa,xb,xc,xd^-1,xc^-1,xb^-1])),[[4,iarel(2,[xa,xb,xc,xa^-1,xb^-1,xc^-1])],[0,iw(iarel(2,[xa,xb,xc,xd^-1,xc^-1,xb^-1]))]]),
];
lemma7pt4:=[
#Equation 20:
applyrels(theta([["M",xd,xb]],iarel(4,[xa,xd,xc])),[[4,iarel(1,[xc,xb^-1,xa,xd^-1])],[4,cyw(3,iw(iarel(4,[xa,xb,xc])))],[4,cyw(3,iw(iarel(4,[xa,xd,xc])))],[1,iw(iarel(1,[xc,xb^-1,xa,xd^-1]))]]),

#Equation 21:
applyrels(theta([["M",xd,xb]],iarel(4,[xa,xb,xc])),[[0,iw(iarel(4,[xa,xb,xc]))]]),

#Equation 22:
applyrels(theta([["M",xb,xc^-1]],iarel(1,[xa,xb,xc,xd])),[[6,exiarel(1,[xc,xd,xb])],[4,iw(exiarel(1,[xc,xd,xb]))],[2,iarel(3,[xb,xd,xc,xa,xc])],[2,iw(iarel(7,[xa,xb,xc,xd]))],[5,iw(iarel(4,[xc,xd,xa]))],[1,iw(iarel(1,[xa,xb,xc,xd]))]]),

#Equation 23:
applyrels(theta([["M",xd,xe]],exiarel(3,[xa,xb,xc,xd])),[[2,iarel(1,[xb,xd,xa,xe])],[4,iarel(1,[xc,xd,xb,xe])],[3,iarel(1,[xc,xd,xa,xe])],[0,iw(exiarel(3,[xa,xb,xc,xd]))],[3,iw(exiarel(3,[xa,xb,xc,xe]))],[2,iarel(1,[xa,xe,xc,xd])],[3,iarel(1,[xb,xe,xc,xd])],[1,iarel(1,[xa,xe,xb,xd])]]),

#Equation 24:
applyrels(theta([["M",xd,xe]],exiarel(3,[xa,xb,xc,xe])),[[0,iw(exiarel(3,[xa,xb,xc,xe]))]]),
];
lemma7pt5:=[
#Equation 25:
applyrels(theta([["M",xf,xe]],iarel(8,[xa,xb,xc,xd,xf])),[[6,cyw(-3,iw(iarel(8,[xa,xb,xc,xd,xe])))],[0,iarel(3,[xa,xb,xc,xd,xe^-1])],[5,iw(iarel(3,[xa,xb,xc,xd,xe^-1]))],[1,iw(iarel(8,[xa,xb,xc,xd,xf]))]]),

#Equation 26:
applyrels(theta([["M",xf,xe]],iarel(8,[xa,xb,xc,xd,xe])),[[0,iw(iarel(8,[xa,xb,xc,xd,xe]))]]),

#Equation 27:
applyrels(theta([["M",xc,xe^-1]],iarel(9,[xa,xb,xe,xd])),[[1,iarel(2,[xc,xd,xa,xe,xd,xa])],[0,iw(iarel(9,[xa,xb,xc,xd]))],[5,iw(iarel(9,[xa,xb,xe,xd]))],[12,exiarel(1,[xe,xd^-1,xc])],[12,iw(exiarel(1,[xe,xd^-1,xc]))],[8,iw(iarel(8,[xe,xb,xa,xc,xd]))],[12,iarel(2,[xe,xb,xa,xc,xb,xa])],[10,iarel(1,[xe,xd,xc,xd])],[9,iw(iarel(1,[xe,xd,xc,xd]))],[9,iarel(3,[xc,xa,xb,xe,xd])],[8,iarel(3,[xe,xa,xd,xc,xd])],[5,iarel(3,[xe,xa,xb,xc,xd^-1])],[3,iarel(2,[xe,xa,xb,xc,xb,xa])],[4,iarel(2,[xe,xd,xa,xc,xb,xa])],[3,iarel(3,[xe,xa,xb,xc,xd])],[4,iarel(3,[xe,xd,xa,xc,xd])],[3,iarel(2,[xc,xa,xd,xe,xd,xa])],[2,iarel(2,[xc,xa,xd,xe,xa,xb])]]),

#Equation 28:
applyrels(theta([["M",xc,xe^-1]],iarel(9,[xa,xb,xc,xd])),[[3,iarel(1,[xa,xb^-1,xc,xe])],[2,iw(iarel(1,[xa,xb^-1,xc,xe]))],[1,iw(iarel(9,[xa,xb,xc,xd]))],[8,iarel(6,[xc,xe,xd])],[13,iw(iarel(6,[xc,xe,xd]))],[13,iarel(5,[xc^-1,xe^-1,xd])],[8,iw(iarel(5,[xc^-1,xe^-1,xd]))],[10,iarel(5,[xc^-1,xd^-1,xe^-1])],[7,iw(iarel(5,[xc^-1,xd^-1,xe^-1]))],[4,iarel(2,[xc^-1,xe^-1,xd^-1,xc,xb,xa])]]),

#Equation 29:
applyrels(theta([["M",xd,xb]],iarel(9,[xa,xd,xc,xd])),[[5,iarel(1,[xa,xb^-1,xc,xb])],[5,cyw(-2,iw(iarel(9,[xa,xb,xc,xd])))],[4,iw(iarel(1,[xa,xb^-1,xc,xb]))],[1,iw(iarel(9,[xa,xb,xc,xb]))],[6,iarel(1,[xa,xd^-1,xc,xb])],[5,iarel(1,[xa,xd^-1,xc,xd])],[0,iarel(1,[xc,xb^-1,xa,xd])],[1,iw(iarel(9,[xa,xd,xc,xd]))],[3,iarel(1,[xa,xd,xc,xd])],[3,iw(iarel(9,[xa,xd,xc,xb]))]]),

#Equation 30:
applyrels(theta([["M",xd,xb]],iarel(9,[xa,xb,xc,xb])),[[0,iw(iarel(9,[xa,xb,xc,xb]))]]),

#Equation 31:
applyrels(theta([["M",xd,xb]],iarel(9,[xa,xd^-1,xc,xd])),[[1,iw(iarel(9,[xa,xd^-1,xc,xb]))],[9,iarel(1,[xa,xd,xc,xb])],[8,iw(iarel(1,[xa,xd,xc,xb]))],[5,iw(iarel(9,[xa,xd^-1,xc,xd]))],[7,iw(iarel(5,[xc,xd,xa]))],[7,iarel(5,[xc,xd,xa])],[0,cyw(3,iarel(9,[xa,xb^-1,xc,xd^-1]))],[5,iw(iarel(9,[xa,xb^-1,xc,xb]))]]),

#Equation 32:
applyrels(theta([["M",xd,xb]],iarel(9,[xa,xb^-1,xc,xb])),[[0,iw(iarel(9,[xa,xb^-1,xc,xb]))]]),

#Equation 33:
applyrels(theta([["M",xf,xe]],iarel(8,[xa,xf,xc,xd,xf])),[[3,iarel(1,[xd,xe^-1,xa,xe])],[6,cyw(1,iarel(9,[xa,xe,xd,xf]))],[11,cyw(1,iw(iarel(1,[xd,xe^-1,xa,xe])))],[13,iarel(9,[xa,xe,xd,xe])],[4,iarel(3,[xa,xc,xf,xd,xe])],[5,iarel(3,[xa,xc,xf,xd,xf])],[4,iw(iarel(8,[xa,xf,xc,xd,xe]))],[10,iw(iarel(3,[xa,xc,xf,xd,xf]))],[12,iw(iarel(3,[xa,xc,xf,xd,xe]))],[10,iw(iarel(8,[xa,xf,xc,xd,xf]))],[11,iarel(1,[xa,xe,xd,xe])],[3,iw(iarel(1,[xa,xe,xd,xe]))],[10,iarel(3,[xd,xf,xc,xa,xe])],[11,iarel(9,[xa,xe^-1,xd,xf])],[8,iarel(1,[xa,xe,xd,xf])],[4,iw(iarel(1,[xa,xe,xd,xf]))],[3,iarel(1,[xd,xe^-1,xa,xe^-1])],[6,iw(iarel(3,[xd,xf,xc,xa,xe]))],[7,cyw(1,iw(iarel(1,[xd,xe^-1,xa,xe^-1])))],[9,iarel(9,[xa,xe^-1,xd,xe])],[13,iarel(3,[xa,xc,xe,xd,xe^-1])],[1,iw(iarel(3,[xa,xc,xe,xd,xe^-1]))],[11,iarel(2,[xa,xc,xe,xd,xf,xc])],[7,iarel(5,[xd,xe^-1,xa])],[9,cyw(2,iw(iarel(5,[xd,xe^-1,xa])))],[11,iarel(3,[xa,xc,xe,xd,xe])],[9,cyw(-1,iw(iarel(8,[xa,xe,xc,xd,xe])))],[8,iw(iarel(3,[xa,xc,xe,xd,xe]))],[7,cyw(-1,iw(iarel(8,[xa,xe,xc,xd,xf])))],[7,iarel(3,[xa,xc,xe,xd,xf^-1])],[2,iw(iarel(3,[xa,xc,xe,xd,xf^-1]))],[6,iarel(3,[xa,xc,xe,xd,xe^-1])],[3,iw(iarel(3,[xa,xc,xe,xd,xe^-1]))],[5,iw(iarel(2,[xa,xc,xe,xd,xf,xc]))]]),

#Equation 34:
applyrels(theta([["M",xf,xe]],iarel(8,[xa,xe,xc,xd,xe])),[[0,iw(iarel(8,[xa,xe,xc,xd,xe]))]]),
];
lemma7pt6:=[
#Equation 35:
applyrels(theta([["M",xb,xd]],exiarel(8,[xa,xb,xc,xd])),
[[5,iw(exiarel(1,[xd^-1,xc,xb]))],[9,exiarel(1,[xd^-1,xc,xb])],[27,iw(exiarel(1,[xd^-1,xa,xb]))],[31,exiarel(1,[xd^-1,xa,xb])],[23,iarel(3,[xb,xd^-1,xa,xc,xa])],[33,iw(iarel(3,[xb,xd^-1,xa,xc,xa]))],
#Down to four commutator transvections
[18,iw(iarel(6,[xa,xd,xc]))],[25,iw(iarel(4,[xa,xd,xb]))],[24,iarel(5,[xa^-1,xd,xc])],[21,iarel(2,[xa,xb,xc,xa^-1,xd^-1,xc])],[22,iarel(3,[xa^-1,xd^-1,xc,xb,xd^-1])],[23,iarel(7,[xb,xa^-1,xd^-1,xc])],[28,iarel(3,[xa^-1,xc,xd^-1,xb,xd^-1])],[28,iw(iarel(5,[xa^-1,xd,xc]))],[35,iarel(6,[xa,xd,xc])],[31,theta([["M",xa,xd^-1]],iarel(2,[xa^-1,xd,xc,xa,xc,xb]))],[32,cyw(-2,iw(iarel(6,[xa,xd,xc])))],[29,iarel(1,[xd,xa,xc,xa])],[32,cyw(2,exiarel(6,[xa,xd,xc]))],
#Down to two commutator transvections
[33,iw(iarel(4,[xc,xa,xd]))],[32,iarel(4,[xd,xa^-1,xc])],[31,iw(iarel(4,[xc^-1,xa,xd]))],[29,iarel(1,[xc,xa,xd,xa])],[25,exiarel(5,[xb,xa,xc,xd,xb,xa])],[34,iarel(4,[xd^-1,xc,xa])],[35,iarel(3,[xa,xc,xb,xd,xc])],[35,exiarel(3,[xa,xb,xc,xd])],[32,iarel(1,[xb,xd,xc,xd^-1])],[28,iw(exiarel(5,[xb,xc,xd,xa,xd,xc]))],[29,iw(exiarel(5,[xb,xc,xd,xa,xb,xd]))],[24,exiarel(5,[xb,xa,xc,xd,xb,xc])],[26,iw(iarel(4,[xd,xc,xb]))],[22,exiarel(5,[xa,xc,xb,xd,xb,xc^-1])],[23,iarel(1,[xb,xd,xc,xd])],[21,iw(exiarel(3,[xa,xb,xc,xd]))],[24,iarel(3,[xa,xb,xc,xd,xc])],[30,iw(iarel(7,[xd,xa,xb,xc]))],[29,iw(exiarel(7,[xa,xb,xc]))],
#Down to conjugation moves only
[14,iarel(4,[xb^-1,xd,xc])],[20,exiarel(5,[xa,xb,xc,xd,xa,xc])],[14,iw(exiarel(5,[xb,xc,xa,xd^-1,xa,xb^-1]))],[15,iw(exiarel(5,[xb,xc,xa,xd^-1,xa,xc^-1]))],[17,iarel(1,[xa,xd^-1,xc,xd^-1])],[18,iarel(1,[xb,xd,xc,xd^-1])],[16,iarel(1,[xa,xd^-1,xb,xd^-1])],[12,iw(exiarel(5,[xd,xc,xa,xb^-1,xa,xc^-1]))],[13,iw(exiarel(5,[xd,xc,xa,xb^-1,xa,xd^-1]))],[14,iw(exiarel(5,[xd,xc,xa,xb^-1,xa,xc]))],[15,iw(exiarel(5,[xd,xc,xa,xb^-1,xd,xc]))],[9,iw(exiarel(5,[xd,xb,xa,xc^-1,xa,xc^-1]))],[10,iw(exiarel(5,[xd,xb,xa,xc^-1,xa,xd^-1]))],[11,iarel(1,[xb,xc^-1,xd,xc^-1])],[7,iw(iarel(4,[xb^-1,xd,xc]))],[3,exiarel(5,[xa,xc,xb,xd,xa,xb])],[6,iw(exiarel(5,[xa,xc,xd,xb,xa,xc^-1]))],[7,iw(exiarel(5,[xa,xc,xd,xb,xa,xd^-1]))],[3,iw(exiarel(5,[xa,xc,xb,xd,xa,xc^-1]))],[4,iw(exiarel(5,[xa,xc,xb,xd,xa,xd^-1]))],[0,iw(exiarel(5,[xa,xb,xd,xc,xa,xc^-1]))],[26,iarel(4,[xd,xc,xa])],[24,exiarel(5,[xd,xc,xb,xa^-1,xd,xc^-1])],[23,exiarel(5,[xd,xc,xb,xa^-1,xb,xd^-1])],[22,exiarel(5,[xd,xc,xb,xa^-1,xc,xd^-1])],[21,exiarel(5,[xd,xc,xb,xa^-1,xd,xb])],[20,exiarel(5,[xd,xc,xb,xa^-1,xd,xc])],[19,exiarel(5,[xd,xc,xb,xa^-1,xd,xb^-1])],[18,exiarel(5,[xd,xc,xb,xa^-1,xd,xc^-1])],[9,iarel(1,[xb,xc,xa,xc])],[12,iarel(4,[xc^-1,xb,xa])],[12,iarel(1,[xb,xc^-1,xa,xc])],[13,iarel(4,[xb^-1,xc,xd])],[7,iw(iarel(4,[xb^-1,xc^-1,xd]))],[9,exiarel(5,[xc,xa,xd,xb^-1,xd,xc^-1])],[7,exiarel(5,[xd,xc,xa,xb^-1,xd,xc])],[7,iw(iarel(4,[xb,xc^-1,xd]))],[3,iarel(4,[xc^-1,xd^-1,xb])],[0,iarel(1,[xd,xc,xb,xc])],[1,iarel(1,[xb,xd,xc,xd])]]),

#Equation 36:
applyrels(theta([["M",xb,xd]],exiarel(7,[xa,xd,xc])),[[1,iarel(3,[xb,xa^-1,xd^-1,xc,xa])],[15,iarel(3,[xb,xd^-1,xa^-1,xc,xa])],[18,exiarel(2,[xa,xd,xc,xb,xd^-1])],[17,iw(exiarel(7,[xa,xd,xc]))],[12,iw(iarel(4,[xa,xc^-1,xd]))],[3,iarel(1,[xd,xc,xa,xc])],[5,iarel(3,[xb,xd^-1,xc^-1,xa,xc^-1])],[7,iw(iarel(4,[xc^-1,xd,xa]))],[8,iarel(3,[xb,xc^-1,xd^-1,xa,xc^-1])],[10,iarel(4,[xc^-1,xd,xa])],[13,iw(iarel(4,[xa^-1,xc^-1,xd]))],[10,iarel(1,[xd,xc^-1,xa,xc])],[15,exiarel(3,[xb,xc,xd,xa^-1])],[8,iarel(1,[xa,xd^-1,xc,xd^-1])],[7,iarel(3,[xb,xc^-1,xd^-1,xa,xd^-1])],[5,iarel(1,[xc,xd,xa,xd])],[5,iw(exiarel(1,[xc^-1,xd^-1,xb]))],[8,iw(exiarel(1,[xd,xc^-1,xb]))],[6,iw(exiarel(5,[xd,xc,xb,xa,xb,xd]))],[10,iw(exiarel(3,[xb,xc,xd,xa^-1]))],[5,iw(exiarel(1,[xd^-1,xc,xb]))],[3,iarel(5,[xb,xd,xc])],[3,exiarel(5,[xd,xc,xb,xa,xb,xd])]])
];

verifyh2ia:=[verifyiarel,thetavsconjaut,exiarelchecklist,thetainverselist,thetaN3list,thetaN4list,thetaN5list,thetaconjrellist,kfromialist,thetavsphilist,rewritethetaR5R6,kernellist,lemma7pt2,lemma7pt3,lemma7pt4,lemma7pt5,lemma7pt6];
