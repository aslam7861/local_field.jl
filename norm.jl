

######################### norm_qadic############################################
##codes to be added in Hecke

function Hecke.norm(a::qadic)
    L = parent(a)
    n = degree(parent(a))
    pr = prod([frobenius(a,i) for  i =1:n]) 
  return coeff(setprecision(pr,L.prec_max),0)
end


function Hecke.trace(a::qadic)
    L = parent(a)
    n = degree(parent(a))
    pr = sum([frobenius(a,i) for  i =1:n])
  return coeff(setprecision(pr,L.prec_max),0)
end


function Hecke.norm_equation(a::padic,L::FlintQadicField)
  r = L(1)
  s = r*L(lift(Hecke.trace(r)^(-1)))*L(lift(log(a)))
  return setprecision(exp(s),L.prec_max)
end

function Hecke.norm_equation(a::qadic,L::FlintQadicField)
   a = coeff(a,0)
   r = L(1)
   s = r*L(lift(Hecke.trace(r)^(-1)))*L(lift(log(a)))
  return setprecision(exp(s),L.prec_max)
end


#### either or funtcion (  a ==b ? "true arg" : "false arg")
###













function basis_qadic(K::FlintQadicField)
  n = degree(K)
  g = gen(K);
  d = Array{typeof(g)}(undef, n)
  b = K(1)
  for i = 1:n-1
    d[i] = b
  b *= g
 end
 d[n] = b
 return d
end

function gens_qadic(c)
# this returns all the generators of fields
   A = qadic[]
   push!(A,gen(c))
   while typeof(norm(gen(c))) != padic
        c = parent(norm(gen(c)))
        push!(A, gen(c))
   end
return A
end
  



# function precision_req(a)
#    


function higher_unit(c::FlintQadicField)
   n = precision(c)
   rr = [i for i in 1:n]
   pi = uniformizer(c)
   r,mr = ResidueField(c)
     i = rand(rr); 
   #d = c(1+mr.g(rand(r))*pi^i)    
   return c(1+inv(mr)(rand(r))*pi^i),i
end

function residue_system_basis(R)

  F,mF = ResidueField(R);
  b = basis(F);

  return [mF\(b[i]) for  i in 1:length(b)];

end



function principal_unit_group_generators_I(c)#::Hecke.LocalField{S, EisensteinLocalField}) where {S <: FieldElem}

    r,mr = ResidueField_ali(c)
    e = Int(absolute_degree(c)//degree(r))
    Fe = []
     n = degree(c)
    p = Int(prime(c))
    for i in 1:Int(floor(e*p/(p-1)))
        if gcd(i,p) == 1
            append!(Fe,i)
        end
    end
    pi = uniformizer(c)
    #b = basis(r)
     bas = [pseudo_inv(mr)(a) for a in basis(r)]
   # U = Array{qadic}(undef, n) #it will be increased by one more unit n+1    
 ##bb = [1+preimage(mr,b[i] )*p^1 for i in 1:length(b)]  ##preimage not defined
   u_gen=Any[]
    prec = precision(c)

  for nu in Fe
      if nu < prec 
         for r in bas
             push!(u_gen, 1+r*pi^nu)
         end    
      end
  end

##  bb = [1+pseudo_inv(mr)(b[i])*p^1 for i in 1:length(b)]
 # U = []
return u_gen
end


function principal_unit_group_generators_II(c);

 ## vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: case II";
  r,mr = ResidueField_ali(c)
    e = Int(absolute_degree(c)//degree(r))
    n = degree(c)
    p = Int(prime(c))


#  e = RamificationIndex(R,PrimeRing(R));
 # p := Integers()!Prime(R);
  mu0 = valuation(e,p)+1;
##(e/(p^(mu0-1)*(p-1)));
  e0 = Int((e//(p^(mu0-1)*(p-1))));

  pi = uniformizer(c);
  prec = precision(c);

  resy = residue_system_basis_II(c);
#//"resy",resy;
  Fe = Any[]
  for i in 1:Int(floor(e*p/(p-1)))
        if gcd(i,p) == 1
            append!(Fe,i)
        end
  end     
  u_gen = Any[];

 ## F := Fe(R);
#  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Fundamental levels:", F;
  for nu in Fe 
    if nu < prec 
      for r in resy 
        push!(u_gen, 1+r*pi^nu);
      end ;
    end ;
  end ;
  push!(u_gen, 1+w_star(c)*pi^(p^mu0*e0));

  return u_gen;

end ;

function principal_unit_group_generators(c)
   
   r,mr = ResidueField_ali(c)
    e = Int(absolute_degree(c)//degree(r))
#    n = degree(c)

 # e := RamificationIndex(R,PrimeRing(R));
  p = Int(prime(c));

  if mod(e ,p-1) != 0 || h2_is_isomorphism(c) || precision(c) < e/(p-1) 
     u_gen =  principal_unit_group_generators_I(c);
  else
     u_gen = principal_unit_group_generators_II(c);
  end ;

  u_gen = reverse(u_gen);
##  //vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Generators:", gens;
  return u_gen;
end ;



#=
function principal_unit_group_generators_qadi(c::FlintQadicField)
    r,mr = ResidueField(c)
    e = Int(degree(c)//degree(r))
    Fe = []
     n = degree(c)
    p = Int(prime(c))
    for i in 1:Int(floor(e*p/(p-1)))
  	if gcd(i,p) == 1
            append!(Fe,i)
	end
    end
    pi = uniformizer(c)
    b = basis(r)    
  #  U = Array{qadic}(undef, n) #it will be increased by one more unit n+1    
 
   
bb = [1+preimage(mr,b[i] )*p^1 for i in 1:length(b)]
# U = []
return bb
end
=#
#function degree(R ::Hecke.QadicRing{FlintQadicField} )



function unit_group_generators_local(c)##LocalField
    u_gen = principal_unit_group_generators(c)
    p = Int(prime(c))
    r,mr = ResidueField_ali(c)
    e = Int(absolute_degree(c)//degree(r))
  #=  Fe = []
     n = degree(c)
    p = Int(prime(c))
    for i in 1:Int(floor(e*p/(p-1)))
        if gcd(i,p) == 1
            append!(Fe,i)
        end
    end=#
   ru,mru = unit_group(r)
 
  gen_exp = length(r)^(Int(ceil(precision(c)//valuation(length(r),p))));
    cycgen = (c(pseudo_inv(mr)(mru(ru[1]))))^gen_exp;
 push!(u_gen,cycgen)
return u_gen;
end

#=
    pi = uniformizer(c)
    b = basis(r)
  #  U = Array{qadic}(undef, n) #it will be increased by one more unit n+1    
   A= Array{qadic}(undef,n+2) #unramirfied case
   for i in 1:length(b)
       A[i] = 1+preimage(mr,b[i] )*p^1
   end
   u,mu = unit_group(r)
     gen_exp = order(r)^(Int(ceil(precision(c)/valuation(order(r),p))))
     gen = (preimage(mr, mu(u[1])))^gen_exp
     A[n+1]= gen
    # A[n+2]= uniformizer(R)
      A[n+2]= uniformizer(c)  #check R
  if typeof(c) == FlintQadicField
      return A
  else
   # typeof(R) ==  Hecke.QadicRing{FlintQadicField}
     return [A[i] for i in 1:length(A)-1]
  end

# bb = [1+preimage(mr,b[i] )*p^1 for i in 1:length(b)]
# U = []
#return A
end     
=#

function unit_group_generators(c::FlintQadicField)  #(c::FlintQadicField)
    r,mr = ResidueField(c)
    e = Int(degree(c)//degree(r))
    Fe = []
     n = degree(c)
    p = Int(prime(c))
    for i in 1:Int(floor(e*p/(p-1)))
        if gcd(i,p) == 1
            append!(Fe,i)
        end
    end
    pi = uniformizer(c)
    b = basis(r)
  #  U = Array{qadic}(undef, n) #it will be increased by one more unit n+1    
   A= Array{qadic}(undef,n+2) #unramirfied case
   for i in 1:length(b)
       A[i] = 1+preimage(mr,b[i] )*p^1
   end
   u,mu = unit_group(r)
     gen_exp = order(r)^(Int(ceil(precision(c)/valuation(order(r),p))))
     gen = (preimage(mr, mu(u[1])))^gen_exp
     A[n+1]= gen
    # A[n+2]= uniformizer(R)
      A[n+2]= uniformizer(c)  #check R
  if typeof(c) == FlintQadicField
      return A
  else
   # typeof(R) ==  Hecke.QadicRing{FlintQadicField}
     return [A[i] for i in 1:length(A)-1]
  end
      
# bb = [1+preimage(mr,b[i] )*p^1 for i in 1:length(b)]
# U = []
#return A
end

 




function multiplicative_group_ali(o::NfOrd)
    return unit_group(o)
end


function generators_ali(u, mu)
    # this returns all generators of Codomain of mu
    n = ngens(u)
    s = Array{NfOrdElem}(undef,n)
    for i = 1:n
       s[i] = mu(u[i])
     end
    return s
    #return [mu(u[i]) for i in 1:n]
end


function group_action_element_ali(psi:: NfToNfMor,mu::Hecke.MapUnitGrp{NfOrd})
   # this is a G action on the unit group 
   #g = domain(mg)
   u = domain(mu)
   L = nf(parent(mu(u[1])))
   #n = ngens(g)
return hom(u,u,[preimage(mu, psi(L(mu(u[j])))) for j in 1:ngens(u) ])
end
 
function group_action_ali(mg,mu)
   # this consists oa all G action on the unit group 
   g = domain(mg)
   u = domain(mu)
   o = parent(mu(u[1])) 
   L = nf(o)
   n = length(g)
   A = Array{GrpAbFinGenMap}(undef, n)
   for i in 1:n
       A[i] = hom(u,u,[preimage(mu, mg(g[i])(L(mu(u[j])))) for j in 1:ngens(u) ])
# A[i] = hom(u,u,[ mu\(o( mg(g[i])(L(mu(u[j]))))) for j in 1:ngens(u) ])
    end
return A;
end 
    



function Sunit_group_action(L,P,psi)
# Let P be a set of primes then this computes the sunit group and and its G-action
    G = domain(psi)
   ol = maximal_order(L)
   fac = prime_divisors(discriminant(ol))
   for i in P
       push!(fac, i)
   end
   fac = sort_seq(fac)
   S =NfOrdIdl[]
   for i in fac
       pp = prime_decomposition(ol,i)
       for p in pp
           push!(S,p[1])
       end
   end
   u,mu = Hecke.sunit_group_fac_elem(S)
   #act =GrpAbFinGenMap[]
   tup_act= Tuple{GrpGenElem,GrpAbFinGenMap }[]
    
    for i in 1:length(G)
     push!(tup_act,( G[i], hom(u,u,[mu\(psi(G[i])(mu(u[j]))) for j in 1:ngens(u)]) ))
    # push!(tup_act,( G[i], hom(u,u,[preimage(mu, psi(G[i])(L( mu(u[j]))) )  for j in 1:ngens(u)]) ))  
     end
return u,mu,tup_act
end  


 
function sunit_action(mu,psi,g)
   u = domain(mu)
   h = psi(g)
return hom(u,u,[mu\(h(mu(u[j]))) for j in 1:ngens(u)])
#return hom(u,u,[preimage(mu, h(elem_in_nf( mu(u[j]))) )  for j in 1:ngens(u)]) 
#elem_in_nf is to bring in number field
end

function random_elt(O)
   B = basis(O)
   n = length(B)
   c = [rand(1:4) for i in 1:n]
return(O(c))
end

function normal_basis_elt(O, psi) #rand==false
    G = domain(psi)
    bool = false 
    bas = basis(O)
    if  !bool
       for i in 1:length(bas)
          D = matrix([coefficients(  psi(g)(elem_in_nf(bas[i]))) for g in G])
          if det(D) != 0 
             return bas[i]
             #break i  
            end
        end
     end
    bool = false
    while !bool
       r = random_elt(O)
       D = matrix([coefficients(  psi(g)(elem_in_nf(r))) for g in G])
          if det(D) != 0
             return r            
          end
      end  

 # if not found then one must try with rando element of ol
end




function sort_seq(A)
   B = typeof(A[1])[]
   for a in A
      if !(a in B)
         push!(B,a)
       end
    end
return B
end




function lattice_gen_theta(psi,P,p,rand)     # :rand =false
   ol = order(P)
   pi = uniformizer(P)
   theta = normal_basis_elt(ol, psi) #: rand = rand)
   v = valuation(theta, P)
   v1 = 1+ Int(floor(ramification_index(P)/(p-1) ))   # absolute_ram_index if over relative 
   v = max(0, v1-v)
   theta = ol( theta*pi^v)
return theta,v
end

#coefficients(elem_in_nf(theta))



function lattice_ali(P,p,psi)
   o = order(P)
   pi = uniformizer(P)
   G = domain(psi)
   bool = false
   for i in 1:100
      while true
          theta,v = lattice_gen_theta(psi, P, p, rand)
          bool = true
          #theta = coefficients(elem_in_nf(theta))
          Gen = [o(psi(g)(elem_in_nf(theta)) ) for g in G ]
          M = matrix([ coefficients(elem_in_nf(x)) for x in Gen])
          bool = rank(M) == length(G)
         if bool 
            break
         end
       end
    end
       
 # do somehting more
# one can choose a large value of second argument
# ZpGtheta := Lattice(M); create this
return theta, v+1
end 



function composition_map(f,g)
  # maps are such that g.f is defined 
 # once inverse(mu) in unit group works then replace g
  L = domain(f)
  M = codomain(f) 
 @assert M == domain(g)
  
#=  gf = function(a)
          g\(f(a))
        end 
  fg_i = function(b)
             f\(g(b))
          end 
return Hecke.MapFromFunc(gf,fg_i) 
=#
return f*g
end  
         
function random_ali(o)
     b = basis(o)
     L = nf(o)
     n = degree(L)
     r = [rand(1:4) for i in 1:n]
return sum( [ r[i]*b[i] for i in 1:n])
end


function exp_truncated(x::qadic,n)

return sum([ x^i//factorial(i) for i in 0:n])
end


function Completion_list(P::NfOrdIdl,psi)
    L=nf(order(P))
    lp,mlp = completion(L,P)
    G = domain(psi)
    Gp = [x for x in G if psi(x)(L(P.gen_two)) in P && psi(x)(L(P.gen_one)) in P]
    #maps = [psudo_inv(mlp)*psi(g)*mlp for g in Gp]
    function psip(g)
          pseudo_inv(mlp)*psi(g)*mlp
     end  
return lp,mlp,Gp,psip
end

# func< alpha, N | &+( [  alpha^n/ Factorial(n) : n in [0..N] ] ) >;

function compute_lpmult_mod(L,P,psi,list,theta,m)
# computes the module with respect to ideal
   lp = list[1]
   inc_lp = list[2]
   psil = list[4]
   Gp = list[3]
   pi = uniformizer(P)
   G = domain(psi)
   GG = [x for x in G]
   H = [x for x in Gp]
   HH = [x for x in H]
   ol = maximal_order(L)
   pil = uniformizer(lp) #check this
   q,mq = quo(o,P^m)
   qmul, i_qmul = unit_group(q)
  phi_l_q = mq*pseudo_inv(i_qmul)
  phi_q_l = i_qmul* pseudo_inv(mq)
 
 p = P.minimum
   N = Int(ceil( Int(m) / ( valuation(theta, P)- ramification_index(P)/(Int(p)-1))))
 expTheta = inc_lp\(exp_truncated(inc_lp(elem_in_nf(theta)),  N ))
  conjq = [ phi_l_q(ol( psi(g)(elem_in_nf(expTheta)) )) for g in HH]
  S, pi_Qmal_S = quo(qmul , sub(qmul,conjq)[1] );  #  check sub function
  phi_l_S = phi_l_q*pi_Qmal_S;

 # phi_l_S = function(a)
#               pi_Qmal_S(phi_l_q(a))
#            end
#  phi_l_S_i = function(a)
#                 phi_l_q_i(pi_Qmal_S\(a)) 
#               end
#
  # phi_S_l := inverse(phi_l_S);
  #########
 #// G-Wirkung auf S
   function actS(g,s)
          phi_l_S(ol(psi(g)(elem_in_nf(phi_l_S\(s)))))
    end
    #actS := map< car<G, S> -> S  |  x :-> phi_OL_S( psiG(x[1])( phi_S_OL(x[2]) ) ) >;
  #  // Z-Erzeuger
    ZgenS = [S[i] for i in 1:ngens(S) ];
    
#    // G-Wirkung auf L_P^\times / X  als Matrizen
 #check from here
    #M = Vector{fmpz_mat}[];
      M = fmpz_mat[]
     for k in 1:length(HH) # [1..#HH] do
        g = HH[k];
        bilder =Vector[];
       # bilder =fmpz_mat[];
     #  // Wirkung auf pi lokal
        bild = psip(g)(pil);
        
         seq = (phi_l_S(ol( inc_lp\(bild//pil)))).coeff;
          push!(bilder, append!([1], seq));
           #bilder = Vector(append!([1], seq))
         #push!(bilder, matrix(FlintZZ,1, ngens(S)+1,append!([1],seq) ))
       

        #bilder := bilder cat [ [0] cat ElementToSequence(actS(g,s) ) : s in ZgenS];
       # bilder := bilder cat [ [0] cat (actS(g,s)).coeff) : s in ZgenS];
         bilder = vcat(bilder, [append!([0], (actS(g,s)).coeff) for s in ZgenS])
     # bilder = vcat(bilder, [matrix(FlintZZ,1, ngens(S)+1, append!([0], (actS(g,s)).coeff)) for s in ZgenS])
        #push!(M, bilder)  
       push!(M ,  matrix(ZZ, bilder) );
    end 
    
   Y =free_abelian_group(length(ZgenS)+1);
  # mmY := map< H -> Aut(Y) | g :-> hom< Y -> Y | 
   #     y :-> Y!Eltseq(Vector(Eltseq(y))*M[ Index(HH,g)]) > >;
    function mmY(g)
           hom(Y,Y,[Y( y.coeff * M[position_ali(g,HH)]) for y in gens(Y) ])             
       end

     X, qX = quo(Y, [order(ZgenS[i])* Y[i+1] for i in 1:length(ZgenS) ]);
   
   #  mmX := map< H -> Aut(X) | g :-> hom< X -> X | x :-> qX( x@@qX @ mmY(g) ) > >; 
     function mmX(g)
           hom(X,X,[ qX( mmY(g)(qX\(x))) for x in gens(X)])     
          end


    function lp_X(x)
         qX( Y(  append!([valuation(x)], (phi_l_S(ol(inc_lp\(  x// pil^(valuation(x))))  ) ).coeff )  ))
     end
    function X_lp(y)
          yy = (qX\(y)).coeff
           rem_1st= Vector([yy[i] for i in 2:length(yy)])
         pil^(yy[1]) * inc_lp(elem_in_nf( phi_l_S\( S( rem_1st)) ))
     end


   
    return X, mmX, lp_X, X_lp;
end 

function max_index(A)
    m = maximum(A)
    for i = 1:length(A)
        if A[i]==m
           return m,i
        end
     end
end




function ResidueField_ali(K)##::Hecke.LocalField{S, EisensteinLocalField}) where {S <: FieldElem}
  if typeof(K) == FlintPadicField || typeof(K)== FlintQadicField
      return ResidueField(K) 
  end
  k = base_field(K)
  while !(typeof(k) == FlintPadicField || typeof(k)== FlintQadicField)
  ##if typeof(k) ==  Hecke.LocalField{qadic, Hecke.EisensteinLocalField}
     k = base_field(k) ##until FlintQadicField
  end
  ks, mks = ResidueField(k)

  function proj(a)##::LocalFieldElem)
    @assert parent(a) === K
    for i = 1:degree(a.data)
      if valuation(coeff(a, i)) < 0
        error("The projection is not well defined!")
      end
    end
    return mks(coeff(a, 0))
  end

  function lift(a::fq_nmod)
    @assert parent(a) === ks
    return setprecision(K(mks\(a)), 1)
  end
   mp = MapFromFunc(proj, lift, K, ks)

  return codomain(mp) ,mp ## MapFromFunc(proj, lift, K, ks)
end


function position_ali(a,G)
    return  findfirst(x->x==a,G)
end

function cl_residue_system_basis_II(R)
  F,mrf = ResidueField_ali(R);
  w = basis(F);
##//"w",w;
  c = cl_find_w1(R);
##//"c",c;
  max, pos = maximum([c[i]:i in 1:length(c)]);
##//[w[i]^c[i]: i in [1..#w ]];
  w1 = sum[w[i]*c[i]: i in [1..length(w) ]];
##//"w1",w1;
 if pos != 1
    w[pos] = w[1];
  end ;
  w[1] = w1;
  return [mrf(w[i]) : i in 1:length(w) ] ;
end

#=
function localized_aut_group(psi,P,iota, aut)
#this constructs a mapping feom decomposition group of P to automorphisms Lp
    
   G = domain(psi)
   L = domain(psi(G[1]))
   Gp = [g for g in G if psi(g)(L(P.gen_two)) in P && psi(g)(L(P.gen_one)) in P ] 
   Gp = subgroup(G,Gp)[1]
   if G eq Gp 
      Gp = G
   end
  
  OL = domain(aut[1])  #completion
  rts = roots(defining_polynomial(L),L)
  rtsloc = roots(defining_polynomial(OL),OL)
  @ assert length(rts) == length(rtsloc)
  z =Any[]
  for i =1:length(rts)
      S = [valuation(rtsloc[j] - OL( iota(rts[i])) ) for j in 1:length(rtsloc)]
      prec index = max_indec(S)
      z = vcat(z,[index])   
  end
 
  y =Any[]
  for i =1:length((aut))
      S = [valuation( aut[i](rtsloc[1]) - rtsloc[j]) for j in 1:length(rtsloc)]
      prec index = max_indec(S)
      y = vcat(y, [index]) 
  end

 z = [ position_ali(z[i],y) for i in 1:length(z)]
  return Gp, map(Gp,aut,g:-> local_map(g, psi, aut, rts, z)   )
#construct local_map_down
end
 


function local_map( g,psi,aut, rts, z)

   a1 = position_ali(1,z)
   x = psi(g)(rts[a1])
   S = [ x- rts[i] for i in 1:length(rts)] 
   j = position_ali(0, S)
   return aut[z[j]]
end




=#










#####################

#=



function gfc_cyclic(L,p)
   G,psi = automorphism_group(L)
   OL = maximal_order(L)
   prime = prime_factors(discriminant(OL))
   psuh!(prime, p)
   S = NfOrdIdl[]
   for i in P
       for p in prime_decomposition(OL,i)
           push!(S,p[1])
       end
   end
 u,mu = Hecke.sunit_group_fac_elem(S)
 change >>>lattice and completion for all prime ideals>>> then move forward













repeat>>>>>>>>>>
for i in 1:100
         while q < 10
               q = q+1
              if q > 10 ; break ; end 
             end
       end




=#


#function automorphims_ali(o)
#     L = nf(o)
#     g,mg = auotomorphism_group(L)
#     return [hom<o->o | x:->mg(g[i])(L(x)) , y :-> inv(mg(g[i]))(L(y)) >  for i in 1:ngens(g)]
#end
#automorphisms_group of order where it comes as restriction of o


#
#
#rrrrrrr
#
#
#
#
#
#
#
#


#=

function ali_cocycle_lfc_G(L, K, psi, precision, NoNorm)
    local steps, G, OL, Zp, Qp, pi, pi_sigma, pisigmapi, g, i, u_sigma, phi,
          e, OL2ub, OL2, OL1, L1, K1, incl, GG, AutL, AutL1, sigma, psi1,
          OLmal, m, u, bool, gamma1;
#if psi cmpeq 0 then
        _,psi,_ := AutomorphismGroup(L,K);  # compile this
        psi := map<Domain(psi) -> Codomain(psi) | g :-> psi(g^(-1))>;
    end if;
is_equal := func< x,y | setprecision(x,m) ==  setprecision(y,m)
                        where m := minimum([precision(x), precision(y)]) >;


steps := precision+2;
    G = domain(psi);
    OL = ring_of_integers(L);
    #Zp := pAdicRing(RingOfIntegers(OL));
    Qp = Prime_Field(L);
    Zp = ring_of_integers(Qp)
  # d := InertiaDegree(OL,Zp);
    d= Inertia_Degree(L,Qp)  
   
if d == Degree(L,K) then
        pi = uniformizer(K);
        phi = FrobeniusAutomorphism(L,K);
        //phi := FrobeniusAutomorphism(L);
        phi := [g : g in G | &and([ is_equal(psi(g)(b), phi(b)) : b in generators_pad(L,K) ]) ];
        if #phi eq 0 then
            // ungenauer
            phi := FrobeniusAutomorphism(L, K);
            phi := [g : g in G | &and([ Valuation(psi(g)(b) - phi(b)) ge L`DefaultPrecision*95/100 : b in generators_pad(L,K) ]) ];
            //print d;
            //print FrobeniusAutomorphism(L, K)(L.1);
            //print [psi(g)(L.1) : g in G ];
            //print G;
        end if;
        phi := phi[1];
        GG := [phi^i : i in [0..#G-1]];
        return map< car<G,G> -> L | x :-> (Index(GG, x[1])+Index(GG,x[2])-2 lt #G select L!1 else pi) >;
    end if;

            L1 := L;
            K1 := K;
            e := RamificationIndex(L1,K1);
            OL1 := RingOfIntegers(L1);
            OL2 := ext<OL1 |e>;
 u := UniformizingElement(K1)/UniformizingElement(L1)^e;
        vprintf CocycleLFC, 1: "Solve Norm equation... ";
       // vtime   CocycleLFC, 1: bool, gamma1 := MyNormEquation(OL2,m,OL1!u);
        vtime   CocycleLFC, 1: gamma1 := ClNormEquation(OL2,OL1!u);

   pi:= gamma1*UniformizingElement(L1);
if Precision(L) eq Infinity() then
            vprint CocycleLFC, 1: "Switch back to unbounded precision";
            pi := OL2ub!pi;
            OL2 := OL2ub;
        else
            pi := OL2!pi;
        end if;
       phi := FrobeniusAutomorphism(OL2, OL);
 //    phi := FrobeniusAutomorphism(OL2);// "this makes problem in the following action";
        frobAction, GAction, frobIndex := galois_act_L_tensor_Knr(OL, OL2, psi, phi);
        pi_sigma := [GAction(g,<pi : i in [1..d]>)[1] : g in G];
        pisigmapi := [ OL2!(pi_sigma[i]/pi) : i in [1..#pi_sigma]];
        vprintf CocycleLFC, 1: "Solve Frobenius equations... ";
        vtime  CocycleLFC, 1: u_sigma, phi := FrobeniusEquation(pisigmapi, steps, OL);
    end if;
 assert &and({Valuation(phi(u_sigma[i])/u_sigma[i] - pisigmapi[i]) ge steps : i in [1..#u_sigma]});
 d := InertiaDegree(OL,Zp);
    L2 := FieldOfFractions(OL2);
    prodL2 := Domain(frobAction);
    prodOL2 := CartesianProduct([OL2 : y in [1..d] ]);

    tup_sigma := [];
    GG := [g : g in G];
  for g in GG do
        ind := Index(GG,g);
        frobIdx := frobIndex[ind];
        if frobIdx eq 0 then
            frobIdx := d;
        end if;
        Append(~tup_sigma, prodOL2! < u_sigma[ind] * ( i le frobIdx select 1 else  pi_sigma[ind] ) : i in [1..d] > );
    end for;

 c := map<car<G,G> -> prodL2   | x  :->   // x = <x[1], x[2]>
                tupelQuotient(
                    tupelProduct(
                        GAction(x[1], tup_sigma[Index(GG, x[2])]),
                        tup_sigma[Index(GG, x[1])]
                    ),
                    tup_sigma[Index(GG, x[1]*x[2])]
                )
            >;

 c := precompute_map(c);
 assert Minimum([ Minimum([Valuation(y[1]-y[i]) : i in [1..#y]])
        where y is c(x) :  x in Domain(c)]) ge (precision+1);
    if Degree(Codomain(c)[1]) ge 2 then
        // erste Komponente in L modulo pi^(precision+1)
        assert Minimum([ Minimum([ Valuation(z) : z in ElementToSequence(y[1])[2..Degree(Parent(y[1]))]])
            where y is c(x)  :  x in Domain(c)]) ge (precision+1);
    end if;
 gamma := map< Domain(c) -> FieldOfFractions(L) | x :->  ( elem_to_seq(c(x)[1], L)[1] )^(-1) >;

    return gamma;
end function;







=#

function Prime_Field(L)
   u = uniformizer(L)
   for i = 1:absolute_degree(L)
      l = parent(Hecke.norm(u))
       if degree(l) == 1
          break
       end
      u = uniformizer(l)
    end 
 return l
end
    



