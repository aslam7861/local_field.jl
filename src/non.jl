

function non(X; revers= false)
  F = []
  for i in 1:size(X)[2]
     S = Int64[]
     n = 0
     for j in 1:size(X)[2]
         if revers == true
            if all( [ X[k,i] > X[k,j] for k in 1:size(X)[1] ])
               push!(S ,j)
               elseif all([ X[k,j] > X[k,i] for k in 1:size(X)[1] ])
                n = n+1
              end
         else
             if all( [ X[k,i] < X[k,j] for k in 1:size(X)[1] ])
               push!(S ,j)
             elseif all([ X[k,j] < X[k,i] for k in 1:size(X)[1] ])
                n = n+1
          
             end
          end
     end
     push!(T,S)
     if n == 0
        push!(F,i)
     end
   end
   return F
end

function nondomsort(X; revers = false)  #; reverse = false)
    Z = X 
    A = non(X; revers =revers )
    B = [A]
    while size(X)[2]-length(A)> 0
      for i in reverse(A)   ##no need to sort it again because its in ascending
          X = X[:, 1:end .!=i]
      end
      if size(X)[2] == 1
         return push!(B, [ findfirst(i-> X[1:size(X)[1],1] == Z[1:size(Z)[1],i], 1:size(Z)[2]) ])
      end
     A = non(X; revers = revers)
     AA = []
     for k in A
       push!(AA,findfirst(i-> X[1:size(X)[1],k] == Z[1:size(Z)[1],i], 1:size(Z)[2]))
     end
     push!(B,AA)
   end
return B
end
#####################example####################
#=X =
       [0 2 3 3 5 5
       3 2 1 4 5 6
       2 1 3 5 5 7 
       ]
X=rand(3,10)
nondomsort(X), nondomsort(X;revers =true)
=#
#=


function nds(X)
  T = Vector{Any}[]
  RNK = []
  F = []
  N = [] 
  I = Any[]
  for i in 1:size(X)[2]
     S = Tuple{Any,Any}[]
    # I = Any[]
     n = 0
    # F1 = []
     for j in 1:size(X)[2]
         if all( [ X[k,i] < X[k,j] for k in 1:size(X)[1] ])
           # push!(S ,j)
           push!(S,(j,n))
         elseif all([ X[k,j] < X[k,i] for k in 1:size(X)[1] ])
                n = n+1
          end
          #append!(S[2],n)
      #  append!(I,n)
      end
       push!(I,n)
      push!(T,S)
     # push!(N,I)
     # F1 = [] 
       if n == 0
         rnk = 1
         push!(F,i)
       end
     # push!(I,n)
    end
    push!(RNK,F)
    F1 =F

  #push!(RNK, [F[i][1] for i in 1:length(F)])
 
   i = 1
   while length(F) !=0
     #   Q = Tuple{Any,Any}[]
         Q = Any[]
         for p in F
            for q in T[1]  #1:length(T[i]) 
                n = I[q[1][1]]-1
                if n == 0
                   rnk = i+1
                  # push!(Q, (q,n))
                   push!(Q, q[1][1])
                 end
            end
         end
      i = i+1
      F = Q
    # push!(RNK, [F[i][1] for i in 1:length(F)])
     push!(RNK, F)
    end 

return F1,  RNK 


end


function non_min(X)  #; reverse= false)
  F = []
  for i in 1:size(X)[2]
     S = Int64[]
     n = 0
     for j in 1:size(X)[2]
        # if reverse == true;  (i,j) = (j,i) ; end
         if all( [ X[k,i] < X[k,j] for k in 1:size(X)[1] ])
            push!(S ,j)
         elseif all([ X[k,j] < X[k,i] for k in 1:size(X)[1] ])
                n = n+1
          end
      end
      push!(T,S)
      if n == 0
         push!(F,i)
      end
   end
   return F
end


=#

################### computations example #########3


#=
findfirst(i-> X[1:3,1] == X[1:3,i], 1:size(X)[2])
X=rand(1:10,3,50)
 nondomsort(XXX)
3-element Vector{Vector{Int64}}:
 [1, 2, 3]
 [1, 2]   >>>  is  [4,5] columns
 [1]      >>>  is [6] columns

"In the above result the  columns are to be added "

=#
