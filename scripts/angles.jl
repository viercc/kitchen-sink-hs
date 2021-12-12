using JuMP
using GLPK

# number of possible angles
# θ = [1:n]/n * 2π
n = 6

model = Model(GLPK.Optimizer)

# p[i,j] is the probability the tuple of angles (i/n*2π, j/n*2π, (n-i-j)/n*2π)
@variable(model, p[1:n, 1:n] >= 0)
# q[i] is the marginal probability of each angle (which should be same for the three angle)
@variable(model, q[1:n] >= 0)

@constraint(model, total, sum(q) == 1)
@constraint(model, [i in 1:n], sum(p[i,:]) == q[i])
@constraint(model, [j in 1:n], sum(p[:,j]) == q[j])
@constraint(model, [k in 1:n], sum(p[i,j] for i in 1:n for j in 1:n if 2 * n - i - j == k) == q[k])
for i in 1:n
    for j in 1:n
        if i + j < n || i + j >= 2 * n
            @constraint(model, p[i,j] == 0)
        end
    end
end

#print(model)

optimize!(model)
@show value.(q)

print("p = ")
value.(p)

