


function trivial_sclass_numbers(L,L1,N ,pp) #-> SeqEnum
#{ Compute a sequence of primes such that the S-class number of
#  all subfields of L is trivial. Optionally specify a set of primes
#  which will be included in S. }
#    //print "compute subfields";
    subL = [ L, L1,N ];
  #  vprintf GFC, 2: "%o subfields ", #subL;
  #  //"Bach bound is more expensive than by GRH below";
   # SetClassGroupBounds("GRH");
   
    for F in subL 
        OF = maximal_order(F);
        CG, m = class_group(F);
         S=NfOrdIdl[]
         for p in pp
             for a in prime_decomposition(OF,p)
             push!(S,a[1])
           end
         end     
  #   //print "compute S";
       # S := &cat([  [Ideal(x[1]) : x in Decomposition(F,p)]  : p in primes]);
        CGmod, qCG = quo(CG , [m\s for s in S]);
        qq=[i for i in 1:50 if isprime(i)]
          while length(CGmod) > 1
             for i in qq
                s = prime_decomposition(OF, i)
                CGmod, qCG = quo(CG , [m\a[1] for a in s]);
                 if length(CGmod) == 1
                   push!(pp,i)
                   break
                end
    #          end
#          end
         for x in s
            push!(S,x[1])
         end
        end        
       end  
  #=      while #CGmod gt 1 do
/*            q := Generator(CGmod.1 @@ qCG @m meet Integers());
            // q muss nicht prim sein!
            //S cat:= [Ideal(x[1]) : x in Decomposition(F,q)];
            S cat:= &cat([[Ideal(x[1]) : x in Decomposition(F,p[1])] : p in Factorization(q)]);
            CGmod, qCG := quo<CG | [s @@ m : s in S]>;
        end while;
=# 
   #     primes := Sort(Setseq({Generator(s meet Integers()) : s in S}));
    #    //print primes;
    end 
  #  vprintf GFC, 2: " done.";

    return pp
end 


function prime_field(c)
   a= c(1)
  K= parent(norm(a))
  @assert degree(K)==1
return K
end



function h2_is_isomorphism(R)
  p = Int(prime(R))
  pi = uniformizer(R);
   rf,mrf = ResidueField_ali(R);
  rfy,y = PolynomialRing(rf,"y")
  e = Int( absolute_degree(R)// degree(rf))
  eps = -p * pi^-e;
  h22 = y^(p-1)-mrf(eps);
 ## return not HasRoot(h22) and not Degree(h22) eq 1;
  return isirreducible(h22) && !(degree(h22) ==  1);
end 

function w_star(R)
   p = Int(prime(R))
   pi = uniformizer(R)
   rf,mrf = ResidueField_ali(R)
   e = Int( absolute_degree(R)// degree(rf))
   eps = -p*pi^-e
   w = basis(rf)
   rfy,y = PolynomialRing(rf,"y")
   ##  C =cartesiapower([0:p-1],2) use cartesiapower for length(w) >3""
   C = Base.Iterators.product([[i for i in 0:Int(p)-1] for i=1:length(w)]...)
   C=[c for c in C]
 
#####
   cc=Any[]
   for i in 1:p
     for j in 0:p^(length(w)-1)-1
        push!(cc,C[i+p*j])
     end
   end 
   @assert length(cc) == p^(length(w))
   ##one can ignore above by transpose and work with C down 
   for c in cc 
     str = sum([w[i]*c[i] for i in 1:length(w) ])
     h = y^p-mrf(eps)*y-str
    if isirreducible(h)
       return pseudo_inv(mrf)(rf(str)) 
    end
  end 
end



function eltseq(a)
    L = parent(a)
    B = basis(L)
    n = length(B)
    A = typeof(coeff(a,0))[]
    for i in 0:n-1
      push!(A,Int(coeff(a,i)))
    end
return A
end

function eltseq(a::fq_nmod)
    L = parent(a)
    B = basis(L)
    n = length(B)
    #A = typeof(coeff(a,0))[]
    A= Any[]
    for i in 0:n-1
      push!(A,Int(coeff(a,i)))
    end
return A
end

# unit group for local field

function cl_find_w1(R)
#// subroutine for cl_residue_system_basis_II(
  rf,mrf = ResidueField_ali(R);
  w = basis(rf);
  pi = uniformizer(R);
  p = Int(prime(R));
   e = Int( absolute_degree(R)// degree(rf))
#  e := RamificationIndex(R,PrimeRing(R));
  eps = mrf(-p * pi^-e);
  mu0 = valuation(e,p)+1;
    
rfy,y = PolynomialRing(rf,"y")
    
 rts = roots(y^(p^(mu0-1)*(p-1))-eps,rf);   ## Magma has bug here in this line
 @assert length(rts) != 0
 # for r in rts  
    # return Flat(r[1]);
  
   return eltseq(rts[1] )
  # end
end;

########## how to find eltseq(gen(rf))###############################
         
function residue_system_basis_II(R)
  F,mrf = ResidueField_ali(R);
  w = basis(F);
  c = cl_find_w1(R);
  lst =  [c[i] for i in 1:length(c)];
 ## max, pos = maximum([c[i] for i in 1:length(c)]);  
   max = maximum(lst)
   pos = position_ali(max,lst)
 ##[w[i]^c[i]: i in [1..#w ]];
  w1 = sum([w[i]*c[i] for i in 1:length(w) ])
##"w1",w1;
 if pos != 1
    w[pos] = w[1];
  end ;
  w[1] = w1;
  return [pseudo_inv(mrf)(w[i]) for i in 1:length(w)];
end




function residue_system(R)

  F,mF = ResidueField(R);
  b = basis(F);
  p = characteristic(F); 
  L = [i for i in 0:Int(p)-1];
#  C = CartesianPower(L,#b);
#  does not work so alternative
   C = Tuple{fmpz, fmpz}[]
    for i in L
        for j in L
           push!(C, (i,j))
        end 
    end   

  res_sys = qadic[];
  for x in C 
    push!(res_sys, pseudo_inv(mF)(sum([x[i]*b[i] for  i in 1:length(b)])))
  end
  return res_sys;

end 



function residue_system_basis(R)

  F,mF = ResidueField_ali(R);
  b = basis(F);

  return [pseudo_inv(mF)(b[i]) for  i in 1:length(b)];

end 

function random(u)
    n = ngens(u)
    r = [rand(1:3) for i in 1:n]
 return sum([r[i]*u[i] for i in 1:n])
end;


function position_ali(a,G)
    return  findfirst(x->x==a,G)
end



function inverse_ali(h)
#=  A = domain(mu)
  B = codomain(mu)
  h = function(x)
           mu\(x)
      end
return h
=#
return pseudo_inv(h)
end





###############################################ramification polygon############

function ramification_polygon(f)  # -> SeqEnum
#{Computes the RamificationPolygon of an Eisenstein polynomial}

 #       require LeadingCoefficient(f) eq 1: "Polynomial is not monic.";
  #      assert2 IsEisenstein(f);
        
        n = degree(f);
        K = parent((coefficients(f))[1]);
        p = Int(prime(K))
        e_K = ramification_index(K);
       #e_K =1 #unramified case only  
#=      for POLY in extension
         p0  = iota\(lp(prime(lp)))
         NF = parent(p0)
         ONF = maximal_order(NF)
         e_K = ramification_index(prime_decomposition(ONF,ZZ(p0)))
=#
        r = valuation(n,p);
        cffs = coefficients(f)

      if e_K != 1
         tp= typeof(valuation(cffs[length(cffs)-1]))
         Val =tp[]
           for j =0:n
               if Hecke.norm(cffs[j])!=0 
                  push!(Val, e_K*n*valuation(cffs[j]))   #valuation is not exact as it should in crease e.g L(3) is of valuation e
               #ext<L|e>(p) has valuation 1 which is  not true
                else push!(Val,e_K*n*tp(precision(K)) )
               end      
           #Val = [e_K*n*valuation(cffs[j]) for j in 0:n if ];
         end
      else
        Val = [e_K*n*valuation(coefficients(f)[j]) for j in 0:n ];
      end 
   
        L = Any[];

        for i in 0:r-1 #    // valuation of p^i coefficients
                valbinom = 0;
pts  = [  (Val[p^i+1] + p^i - n) ]; #//16 Nov 2017 we change it because f:=x^9+9*x+3; didn't work.
                for j in p^i+1:n #  // recursionformula to compute valuation of binomial coefficients
                        valbinom = valuation(j,p) - valuation(j - p^i,p) + valbinom;
                        push!(pts, e_K*n*valbinom + Val[j+1] + j - n);
                end
push!(L,(p^i-1,minimum([pts[i] for  i in 1:length(pts)])) );#//16 Nov 2017 we change it because f:=x^9+9*x+3; didn't work.
        end
       push!(L,(p^r-1,0)); #// valuation always zero 
        k = 1;
        V = [L[1]];

       while L[k][2] !=0  #// exit condition needs monic poly
                delta = [(L[i][2]-L[k][2])//(L[i][1]-L[k][1]) for i in k+1:length(L)];
                min = minimum(delta);
                j = position_ali(min, delta) + k;
               # h = Index(delta, min, j-k+1);
                #@assert h ==0 
                #=while h ne 0 do
                        j := h+k;
                        h := Index(delta, min, j-k+1);
                end while;
                =#

                push!(V, L[j]);
                k = j;
        end

        if n-1 != V[length(V)][1]
                Push!(V,(n - 1,0));
        end ;

        return V;
end




function ramification_polygon_over_unramified(f)  # -> SeqEnum
#{Computes the RamificationPolygon of an Eisenstein polynomial}

 #       require LeadingCoefficient(f) eq 1: "Polynomial is not monic.";
  #      assert2 IsEisenstein(f);

        n = degree(f);
        K = parent((coefficients(f))[1]);
        p = Int(prime(K))
       # e_K = ramification_index(K);
       e_K =1 #unramified case only  
#=      for POLY in extension
         p0  = iota\(lp(prime(lp)))
         NF = parent(p0)
         ONF = maximal_order(NF)
         e_K = ramification_index(prime_decomposition(ONF,ZZ(p0)))
=#
        r = valuation(n,p);

        Val = [n*valuation(coefficients(f)[j]) for j in 0:n ];
        L = Any[];

        for i in 0:r-1 #    // valuation of p^i coefficients
                valbinom = 0;
pts  = [  (Val[p^i+1] + p^i - n) ]; #//16 Nov 2017 we change it because f:=x^9+9*x+3; didn't work.
                for j in p^i+1:n #  // recursionformula to compute valuation of binomial coefficients
                        valbinom = valuation(j,p) - valuation(j - p^i,p) + valbinom;
                        push!(pts, e_K*n*valbinom + Val[j+1] + j - n);
                end 
push!(L,(p^i-1,minimum([pts[i] for  i in 1:length(pts)])) );#//16 Nov 2017 we change it because f:=x^9+9*x+3; didn't work.
        end
       push!(L,(p^r-1,0)); #// valuation always zero 
        k = 1;
        V = [L[1]];

        while L[k][2] !=0  #// exit condition needs monic poly
                delta = [(L[i][2]-L[k][2])/(L[i][1]-L[k][1]) for i in k+1:length(L)];
                min = minimum(delta);
                j = position_ali(min, delta) + k;
               # h = Index(delta, min, j-k+1);
                #@assert h ==0 
                #=while h ne 0 do
                        j := h+k;
                        h := Index(delta, min, j-k+1);
                end while;
                =#

                push!(V, L[j]);
                k = j;
        end 

        if n-1 != V[length(V)][1] 
                Push!(V,(n - 1,0));
        end ;

        return V;
end 



#=


intrinsic RamPolyFactors(f::RngUPolElt) -> SeqEnum //, Map
        {f(x) eisenstein -> Faktorisierung von f(x) "zum Verzweigungspolygon"}

        //Lnew<a>:=LocalField(CoefficientRing(f),f);      //für RamPolySubfields(), Berechnung der Teilkörper in RngLocA leichter,
        //L<alpha>,iso:=RamifiedRepresentation(Lnew);     //aber sub<> funktioniert nicht immer...UND ALPHA IST NICHT NS VON f!!

        L<alpha>:=ext<CoefficientRing(f)|f>;

        P<x>:=PolynomialRing(L);
        rho:=Evaluate(f,alpha*x+alpha) div (x*alpha^Degree(f));
        v:=Vertices(NewtonPolygon(rho));
        factors:=[];

        for i in Reverse([2..#v]) do
                N:=Degree(rho);
                m:=Integers() ! v[i-1][1];
                E:=Integers() ! (v[i][1]-v[i-1][1]);
                H:=Integers() ! (v[i-1][2]-v[i][2]);
                e:=E div GCD(E,H);
                h:=H div GCD(E,H);

                LL<beta>:=ext<L|x^e-alpha>;
                R<y>:=PolynomialRing(LL);
                srho:=Evaluate(rho,y*beta^h) / beta^(N*h);//srho;                       //"flatten" the last segment
                c:=[ Coefficient(rho,j)*beta^(h*(j-N)) : j in [m..N] ];
                srho2:=Polynomial(LL,c);
                srho1:=y^m;
                //11;
                hl:=HenselLift(Polynomial(Integers(LL),srho),[srho1,srho2]);//hl;
                //11;
                rho1:=Polynomial(L,Evaluate(hl[1],y/beta^h)*(beta^h)^m);
                rho2:=Polynomial(L,Evaluate(hl[2],y/beta^h)*(beta^h)^(N-m));    //should be over L (unique factor cor. to last segment)
                Append(~factors,rho2);

                rho:=rho1;
        end for;

        factors:=Reverse(factors);//factors;
        factors:=[ Evaluate(rhoi,(x-alpha)/alpha)*alpha^Degree(rhoi) : rhoi in factors ];    //back to f...
        factors[1]:=factors[1]*(x-alpha);

        return factors,L; //, iso;

end intrinsic;


=#
