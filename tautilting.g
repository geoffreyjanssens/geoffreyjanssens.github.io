# GAP-functions and examples related to tau-tilting theory

# Important functions for our paper:
# - MakeRigidTable: this produces the tables found in the appendix.
# - HasseQuiver: this computes the Hasse quiver of the poset of support tau-tilting modules of an algebra A (if A is tau-tilting-infinite, this will not
#                terminate; there is the option to specify a maximal distance from the free module of rank one after which the computation stops)
# - CheckRelativeRigidness: checks whether D is C-presilted (use AllStringMaxLength to see how we represent strings in GAP)
# - CheckSupportOrthogonality: Check whether a vertex e (corresponding to the PIM eA) is not in the support of the tau-rigid
#                              module of a given string
# - GVectorOfString: computes the g-vector of a minimal projective presentation of the string module corresponding to as string.
#
# We also provide functions to create all algebras in Erdmanns classification of tame blocks (as quotients of path algebras that can be used with QPA)

LoadPackage("qpa");

DiagonalJoin := function(L)
        local i, j, m, posr, posc, M;

        if Size(L) = 0 then
            Error("DiagonalJoin expects a list of at least one matrix");
        elif ForAny(L, l -> not IsMatrix(l)) then
            Error("DiagonalJoin expects its arguments to be matrices");
        fi;

        M := NullMat(Sum(List(L, l -> Size(l))), Sum(List(L, l -> Size(TransposedMat(l)))),
            DefaultField(L[1][1][1]));
        posr := 0;
        posc := 0;
        for m in L do
            for i in [1..Size(m)] do
                for j in [1..Size(TransposedMat(m))] do
                    M[posr + i][posc + j] := m[i][j];
                od;
            od;
            posr := posr + Size(m);
            posc := posc + Size(TransposedMat(m));
        od;

        return M;
end;


###############################################################################
# Mutation-related stuff:

TauMinMutateNC := function(M, X)
    # X irreducible; M (+) X support tau-tilting
    local f, Y;
    f := MinimalLeftAddMApproximation(X, M);
    Y := CoKernel(f);
    return Y;
end;

IsBongartzCompletion := function(M, X)
    # X irreducible; M (+) X support tau-tilting
    return not IsZero(Dimension(CoKernel(RightFacMApproximation(M, X))));
end;

HasseQuiver := function(arg)
    # HasseQuiver(A): compute the Hasse-quiver of A (might not terminate)
    # HasseQuiver(A, limit): compute the Hasse-Quiver of A, but stop
    #                        when (at least) limit support tau-tiltings
    #                        have been found
    # returns [lst, Q], where Q is a quiver, and lst corresponds to the
    # vertices of Q, i.e. lst[i] = [M0, ..., Mj], where
    # M0 (+) ... (+) Mj is the support tau-tilting module corresponding
    # to vertex i
    local A, limit, vertex_id, last_layer, new_layer, all_layers, hasse_quiver,
        tup,  i, M, X, Y, vx, new_el, tup2, is_new;

    A := arg[1];
    if Size(arg) = 2 then
        limit := arg[2];
    else
        limit := infinity;
    fi;
    vertex_id  := 2; # vertex 1 is the free module of rank 1
    last_layer := [[1, IndecProjectiveModules(A)]];
    all_layers := [[1, IndecProjectiveModules(A)]];
    hasse_quiver := [ ];
    while Size(last_layer) > 0 and Size(all_layers) <= limit do
        new_layer := [ ];
        for tup in last_layer do
            for i in [1..Size(tup[2])] do
                if Size(tup[2]) <> 1 then
                    M := DirectSumOfQPAModules(tup[2]{Filtered([1..Size(tup[2])],
                                            j -> j <> i)});
                else
                    M := ZeroModule(A);
                fi;
                X := tup[2][i];
                if not IsBongartzCompletion(M, X) then
                    continue;
                fi;
                Y := TauMinMutateNC(M, X);
                if Dimension(Y) = 0 then
                    new_el := tup[2]{Filtered([1..Size(tup[2])], j -> j <> i)};
                else
                    new_el := Concatenation([tup[2]{[1..i-1]}, [Y],
                                             tup[2]{[i+1..Size(tup[2])]}]);
                fi;

                # Check if new_el is isomorphic to a module we found already:
                is_new := true;
                for tup2 in all_layers do
                    if AsSet(List(tup2[2], DimensionVector))
                            <> AsSet(List(new_el, DimensionVector)) then
                        continue;
                    fi;
                    if IsZero(Size(tup2[2])) and not IsZero(Size(new_el)) then
                        continue;
                    elif IsZero(Size(tup2[2])) and IsZero(Size(new_el)) then
                        is_new := false;
                        vx := tup2[1];
                        break;
                    fi;

                    if IsZero(Dimension(CoKernel(RightFacMApproximation(
                            DirectSumOfQPAModules(tup2[2]),
                            DirectSumOfQPAModules(new_el)))))
                        and IsZero(Dimension(CoKernel(RightFacMApproximation(
                            DirectSumOfQPAModules(new_el),
                            DirectSumOfQPAModules(tup2[2])))))
                        then
                        is_new := false;
                        vx := tup2[1];
                        break;
                    fi;
                od;
                if is_new then
                    Add(new_layer, [vertex_id, new_el]);
                    Add(all_layers, [vertex_id, new_el]);
                    vx := vertex_id;
                    vertex_id := vertex_id + 1;
                fi;
                Add(hasse_quiver, [tup[1], vx]);
            od;
        od;
        last_layer := new_layer;
    od;

    return [List(all_layers, x -> x[2]), Quiver(vertex_id-1, hasse_quiver)];
end;


###############################################################################
# Various tools for displaying our objects:

PrettyPrintHasseQuiver := function(lst)
    # Takes the result of HasseQuiver and displays it nicely.
    local i, j, k, isnone;
    for i in [1..Size(lst[1])] do
        Print("* Vertex v", i, ": ");
        for j in [1..Size(lst[1][i])] do
            Print(DimensionVector(lst[1][i][j]), " ");
            if j <> Size(lst[1][i]) then Print("(+) "); fi;
        od;
        if Size(lst[1][i]) = 0 then
            Print("(zero module)");
        fi;
        Print("\n  Emanating arrows:\n");
        isnone := true;
        for j in ArrowsOfQuiver(lst[2]) do
            if SourceOfPath(j) = VerticesOfQuiver(lst[2])[i] then
                Print("       ---> ",TargetOfPath(j), "\n");
                isnone := false;
            fi;
        od;
        if isnone then Print("       (none)\n"); fi;
    od;
end;

# Uses Graphviz (needs to be adapted to work on other systems)
PlotQuiver := function(Q)
    # Only works if graphviz is installed and works properly.
    local fname, fd, q;
	fname := Concatenation(TmpName(), ".dot");
	fd := OutputTextFile(fname, false);
	PrintTo(fd, "digraph quiver {\nnode [shape = circle];");
	for q in ArrowsOfQuiver(Q) do
		PrintTo(fd, Concatenation([String(SourceOfPath(q)),
            " -> ", String(TargetOfPath(q)), "[ label = \"",
			String(q), "\", fontsize=8, fontcolor=blue, tooltip=\"",
			String(q),"\" ];\n"]));
	od;
	PrintTo(fd, "}\n");
	CloseStream(fd);
	if ARCH_IS_MAC_OS_X() then
        Exec(Concatenation("open -a Graphviz ", fname));
    else
        Exec(Concatenation("dot -Tx11 ", fname));
    fi;
end;

# Compute all g-vectors of tau-rigid modules obtainable from the free module of rank one by at most n succesive mutations.

TauRigidsGVectors := function(A, n)
    local Q, lst, lst_supp, m, x, v, el, C;
    Q := HasseQuiver(A, n)[1];
    lst := List(Q, l -> List(l, m -> DimensionVector(TopOfModule(m))-
        DimensionVector(TopOfModule(1stSyzygy(m)))));
    m := Size(SimpleModules(A));
    lst_supp := [ ];
    for v in [1..Size(lst)] do
        el := lst[v];
        for x in [1..m] do
            if ForAll(Q[v], w -> DimensionVector(w)[x] = 0) then
                Add(el, -IdentityMat(m)[x]);
            fi;
        od;
        Add(lst_supp, el);
    od;
    return lst_supp;
end;

###############################################################################
# Examples:
# examples are collected in the global variable "examples". Use
# ListExamples() for an overview

MakeSL2Example := function(f)
    local F, Q, kQ, gens, e, a, rels1, rels2, rels, A, name;
    # F := GF(2^f);
    F := GF(2); # Everything should work over GF(2) as well...
    Q := Quiver(2^f-1, Concatenation(List([0..f-1], j -> List([1..2^f-1],
        i -> [i, (i+2*2^j-1) mod (2^f-1) +1,
        Concatenation("a", String(i), "_", String(j))]))));
    kQ := PathAlgebra(F, Q);
    gens := GeneratorsOfAlgebra(kQ);
    e := gens{[1..2^f-1]};
    a := List([0..f-1], j -> List([1..2^f-1],
                                  i -> gens[2^f-1 + j*(2^f-1) + i]));
    rels1 := Concatenation(List([1..2^f-1], i -> List([1..f],
        j -> a[j][i]*a[j][(i+2^j-1) mod (2^f-1) +1])));
    rels2 := Concatenation(Concatenation(List([1..2^f-1], i -> List([1..f],
        j1 -> List(Filtered([1..f], x -> x <> j1), j2 ->
        a[j1][i]*a[j2][(i+2^j1-1) mod (2^f-1) + 1]
        - a[j2][i]*a[j1][(i+2^j2-1) mod (2^f-1) + 1])))));
    rels := Concatenation(rels1, rels2);
    A := kQ/rels;
    name := Concatenation("F (C_2)^", String(f), " semidirect C_(2^",
        String(f), " - 1)");
    return rec( name := name, A := A, Q := Q, F := F );
end;


# Functions that creacte the algebras from Erdmann's list (for all possible choices of parameters).


MakeD2A := function(k,c)
    local F, Q, kQ, a, b, g, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    A:=kQ/[g*b, a^2-c*(a*b*g)^k, (a*b*g)^k-(b*g*a)^k];
    return A;
end;

MakeD2B := function(k,s,c)
    local F, Q, kQ, a, b, g, e, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1],[2,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    e:=GeneratorsOfAlgebra(kQ)[6];
    A:=kQ/[b*e, e*g, g*b, a^2-c*(a*b*g)^k, (a*b*g)^k-(b*g*a)^k, (g*a*b)^k-e^s];
    return A;
end;

MakeD3A1 := function(k)
    local F, Q, kQ, b, g, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    d:=GeneratorsOfAlgebra(kQ)[6];
    e:=GeneratorsOfAlgebra(kQ)[7];
    A:=kQ/[b*g, e*d, (g*b*d*e)^k-(d*e*g*b)^k];
    return A;
end;

MakeD3B1 := function(k, s)
    local F, Q, kQ, a, b, g, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,1],[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[4];
    b:=GeneratorsOfAlgebra(kQ)[5];
    g:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[a*b, g*a, b*g, e*d, (g*b*d*e)^k-(d*e*g*b)^k, a^s-(b*d*e*g)^k];
    return A;
end;

MakeD3K := function(s, t, u)
    local F, Q, kQ, b, g, d, e, k, l, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,3],[3,2],[1,3],[3,1]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    d:=GeneratorsOfAlgebra(kQ)[6];
    e:=GeneratorsOfAlgebra(kQ)[7];
    k:=GeneratorsOfAlgebra(kQ)[8];
    l:=GeneratorsOfAlgebra(kQ)[9];
    A:=kQ/[b*d, d*l, l*b, g*k, k*e, e*g, (b*g)^s-(k*l)^t, (l*k)^t-(e*d)^u, (d*e)^u-(g*b)^s];
    return A;
end;





MakeSD2A1 := function(k, c)
    local F, Q, kQ, a, b, g, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    A:=kQ/[a^2-c*(a*b*g)^k, b*g*b-(a*b*g)^(k-1)*a*b, g*b*g-(g*a*b)^(k-1)*g*a, (a*b*g)^k*a];
    return A;
end;

MakeSD2A2 := function(k, c)
    local F, Q, kQ, a, b, g, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    A:=kQ/[g*b, (a*b*g)^k-(b*g*a)^k, a^2-(b*g*a)^(k-1)*b*g-c*(a*b*g)^k];
    return A;
end;

MakeSD2B1 := function(k, t, c)
    local F, Q, kQ, a, b, g, e, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1],[2,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    e:=GeneratorsOfAlgebra(kQ)[6];
    A:=kQ/[g*b, e*g, b*e, a^2-(b*g*a)^(k-1)*b*g-c(b*g*a)^k, e^t-(g*a*b)^k, (a*b*g)^k-(b*g*a)^k];
    return A;
end;

MakeSD2B2 := function(k, t, c)
    local F, Q, kQ, a, b, g, e, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1],[2,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    e:=GeneratorsOfAlgebra(kQ)[6];
    A:=kQ/[b*e-(a*b*g)^(k-1)*a*b, e*g-(g*a*b)^(k-1)*g*a, g*b-e^(t-1), a^2-c*(a*b*g)^k, b*e*e, e*e*g];
    return A;
end;

MakeSD3A1 := function(k)
    local F, Q, kQ, b, g, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    d:=GeneratorsOfAlgebra(kQ)[6];
    e:=GeneratorsOfAlgebra(kQ)[7];
    A:=kQ/[b*g, d*e*d-(g*b*d*e)^(k-1)*g*b*d, e*d*e-(e*g*b*d)^(k-1)*e*g*b];
    return A;
end;

MakeSD3B1 := function(k, s)
    local F, Q, kQ, a, b, g, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,1],[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[4];
    b:=GeneratorsOfAlgebra(kQ)[5];
    g:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[a*b, g*a, b*g, a^s-(b*d*e*g)^k, e*d*e-(e*g*b*d)^(k-1)*e*g*b, d*e*d-(g*b*d*e)^(k-1)*g*b*d];
    return A;
end;

MakeSD3B2 := function(k, s)
    local F, Q, kQ, a, b, g, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,1],[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[4];
    b:=GeneratorsOfAlgebra(kQ)[5];
    g:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[e*d, b*g-a^(s-1), g*a-(d*e*g*b)^(k-1)*d*e*g, a*b-(b*d*e*g)^(k-1)*b*d*e];
    return A;
end;

MakeSD3C1 := function(s)
    local F, Q, kQ, b, g, r, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,2],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    r:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[b*d, b*r, r*g, e*g, e*r, r*d, r^s-g*b, r^s-d*e, b*g*b, e*d*e];
    return A;
end;

MakeSD3C2 := function(s, k)
    local F, Q, kQ, b, g, r, d, e, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,2],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    r:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[b*r, r*d, e*r, r*g, g*b-d*e, (g*b)^k-r^s, (b*g)^(k-1)*b*d, (e*d)^(k-1)*e*g];
      # Ermann's book gives the relation "(b*g)^k-r^s" instead of "(g*b)^k-r^s",
      # which implies the relations (b*g)^k=0 and r^s=0. This is a typo, and
      # yields the algebra A from below modulo its socle, which is not symmetric.
      # While we used the relations given in Erdmann's book for our paper, this
      # does not affect the results on tau-tilting modules (as the socle gets
      # factored out anyway). Thanks to Klaus Lux for pointing out the mistake.   
    return A;
end;

MakeSD3D := function(s, k, t)
    local F, Q, kQ, a, b, g, d, e, x, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,1],[1,2],[2,1],[2,3],[3,2],[3,3]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[4];
    b:=GeneratorsOfAlgebra(kQ)[5];
    g:=GeneratorsOfAlgebra(kQ)[6];
    d:=GeneratorsOfAlgebra(kQ)[7];
    e:=GeneratorsOfAlgebra(kQ)[8];
    x:=GeneratorsOfAlgebra(kQ)[9];
    A:=kQ/[d*x, x*e, e*d, b*g-a^(s-1), g*a-(d*e*g*b)^(k-1)*d*e*g, a*b-(b*d*e*g)^(k-1)*b*d*e, x^t-(e*g*b*d)^k];
    return A;
end;

MakeSD3H := function(s, k)
    local F, Q, kQ, b, e, g, d, l, A;
    F:=GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,3],[3,2],[3,1]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    d:=GeneratorsOfAlgebra(kQ)[6];
    e:=GeneratorsOfAlgebra(kQ)[7];
    l:=GeneratorsOfAlgebra(kQ)[8];
    A:=kQ/[d*l-(g*b)^(k-1)*g, l*b-(e*d)^(s-1)*e, b*d*e, g*b*d, e*g];
    return A;
end;










MakeQ2A := function(k, c)
    local F, Q, kQ, a, b, g, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    A:=kQ/[g*b*g-(g*a*b)^(k-1)*g*a, b*g*b-(a*b*g)^(k-1)*a*b, a^2-(b*g*a)^(k-1)*b*g-c*(b*g*a)^k, a^2*b];
    return A;
end;

MakeQ2B1 := function(k, c, s)
    local F, Q, kQ, a, b, g, e, A;
    F:=GF(2);
    Q:=Quiver(2,[[1,1],[1,2],[2,1],[2,2]]);
    kQ:=PathAlgebra(F,Q);
    a:=GeneratorsOfAlgebra(kQ)[3];
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    e:=GeneratorsOfAlgebra(kQ)[6];
    A:=kQ/[g*b-e^(s-1), b*e-(a*b*g)^(k-1)*a*b, e*g-(g*a*b)^(k-1)*g*a, a^2-(b*g*a)^(k-1)*b*g-c*(b*g*a)^k, a^2*b];
    return A;
end;

MakeQ3A2 := function(k)
    local F, Q, kQ, b, g, d, e, A;
    F := GF(2);
    Q := Quiver(3,[[1,2], [2,1], [2,3], [3,2]]);
    kQ := PathAlgebra(F, Q);
    b := GeneratorsOfAlgebra(kQ)[4];
    g := GeneratorsOfAlgebra(kQ)[5];
    d := GeneratorsOfAlgebra(kQ)[6];
    e := GeneratorsOfAlgebra(kQ)[7];
    A := kQ/[b*g*b-(b*d*e*g)^(k-1)*b*d*e, g*b*g-(d*e*g*b)^(k-1)*d*e*g,
        e*d*e-(e*g*b*d)^(k-1)*e*g*b, d*e*d-(g*b*d*e)^(k-1)*g*b*d,
        b*g*b*d, e*d*e*g];
    return A;
end;

MakeQ3B := function(k, s)
    local F, Q, kQ, a, b, g, d, e, A;
    F:= GF(2);
    Q:=Quiver(3,[[1,1],[1,2],[2,1],[2,3],[3,2]]);
    kQ:=PathAlgebra(F,Q);
    a := GeneratorsOfAlgebra(kQ)[4];
    b := GeneratorsOfAlgebra(kQ)[5];
    g := GeneratorsOfAlgebra(kQ)[6];
    d := GeneratorsOfAlgebra(kQ)[7];
    e := GeneratorsOfAlgebra(kQ)[8];
    A := kQ/[b*g-a^(s-1), a*b-(b*d*e*g)^(k-1)*b*d*e, g*a-(d*e*g*b)^(k-1)*d*e*g, e*d*e-(e*g*b*d)^(k-1)*e*g*b, d*e*d-(g*b*d*e)^(k-1)*g*b*d, a^2*b, b*d*e*d];
    return A;
end;

MakeQ3K := function(s, t, u)
    local F, Q, kQ, b, g, d, e, k, l, A;
    F:= GF(2);
    Q:=Quiver(3,[[1,2],[2,1],[2,3],[3,2],[1,3],[3,1]]);
    kQ:=PathAlgebra(F,Q);
    b:=GeneratorsOfAlgebra(kQ)[4];
    g:=GeneratorsOfAlgebra(kQ)[5];
    d:=GeneratorsOfAlgebra(kQ)[6];
    e:=GeneratorsOfAlgebra(kQ)[7];
    k:=GeneratorsOfAlgebra(kQ)[8];
    l:=GeneratorsOfAlgebra(kQ)[9];
    A := kQ/[b*d-(k*l)^(s-1)*k, e*g-(l*k)^(s-1)*l, d*l-(g*b)^(t-1)*g, k*e-(b*g)^(t-1)*b, l*b-(e*d)^(u-1)*e, g*k-(d*e)^(u-1)*d, g*b*d, d*e*g, l*k*e];
    return A;
end;










MakeCircle := function()
    local F, Q, kQ, b, g, d, e, eps1, eps2, eps3, eps4, A;
    F := GF(2);
    Q := Quiver(4, [[1,2], [2,3], [1,4], [4,3], [2,2], [4,4], [1,1], [3,3]]);
    kQ := PathAlgebra(F, Q);
    b := GeneratorsOfAlgebra(kQ)[5];
    g := GeneratorsOfAlgebra(kQ)[6];
    d := GeneratorsOfAlgebra(kQ)[7];
    e := GeneratorsOfAlgebra(kQ)[8];
    eps1 := GeneratorsOfAlgebra(kQ)[9];
    eps2 := GeneratorsOfAlgebra(kQ)[10];
    eps3 := GeneratorsOfAlgebra(kQ)[11];
    eps4 := GeneratorsOfAlgebra(kQ)[12];
    A := kQ/[b*eps1*g, d*eps2*e,
        eps1^2, eps2^2, eps3^2, eps4^2, b*eps1-eps3*b,
        d*eps2-eps3*d, eps1*g-g*eps4, eps2*e-e*eps4];
    return A;
end;

# A few examples of algebras used for testing purposes...

examples := [ ];

MakeExamples := function()
    local ex, kQ, b, g, d, e, k, a, c;
    ex := rec( name := "Adachi-Iyama-Reiten Ex 6.3",
            F := GF(5),
            Q := Quiver(3, [[1,2], [2,3], [3,1]]) );
    kQ := PathAlgebra(ex.F, ex.Q);
    ex.A := kQ/AddNthPowerToRelations(kQ, [ ], 2);
    Add(examples, ex);

    ex := rec( name := "Adachi-Iyama-Reiten Ex 6.4",
            F := GF(5),
            Q := Quiver(3, [[1,2], [2,3]]) );
    kQ := PathAlgebra(ex.F, ex.Q);
    ex.A := kQ/AddNthPowerToRelations(kQ, [ ], 2);
    Add(examples, ex);

    Add(examples, MakeSL2Example(2));

    ex := rec( name := "Square with 4th radical power equal to 0",
        F := GF(5),
        Q := Quiver(4, [[1,2], [2,3], [3,4], [4,1]]));
    kQ := PathAlgebra(ex.F, ex.Q);
    ex.A := kQ/AddNthPowerToRelations(kQ, [ ], 4);
    Add(examples, ex);

    ex := rec( name := "Brauer tree * - * - * - *",
        F := GF(3),
        Q := Quiver(3, [[1,2], [2,1], [2,3], [3,2]]));
    kQ := PathAlgebra(ex.F, ex.Q);
    a := GeneratorsOfAlgebra(kQ)[4];
    b := GeneratorsOfAlgebra(kQ)[5];
    c := GeneratorsOfAlgebra(kQ)[6];
    d := GeneratorsOfAlgebra(kQ)[7];
    ex.A := kQ/[ a*b*a, b*a*b, b*a-c*d, c*d*c, d*c*d, a*c, d*b];
    Add(examples, ex);


    ex := rec( name := "Brauer tree * - * - * - (2*)",
        F := GF(3),
        Q := Quiver(3, [[1,2], [2,1], [2,3], [3,2], [3, 3]]));
    kQ := PathAlgebra(ex.F, ex.Q);
    a := GeneratorsOfAlgebra(kQ)[4];
    b := GeneratorsOfAlgebra(kQ)[5];
    c := GeneratorsOfAlgebra(kQ)[6];
    d := GeneratorsOfAlgebra(kQ)[7];
    e := GeneratorsOfAlgebra(kQ)[8];
    ex.A := kQ/[ a*b*a, b*a*b, b*a-c*d, c*d*c, d*c*d, a*c, d*b, c*e, e*d, e^2-d*c];
    Add(examples, ex);
end;
MakeExamples();

ListExamples := function()
    local i;
    for i in [1..Size(examples)] do
        Print("* ", i, ": ", examples[i].name, "\n");
    od;
end;
#
# Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
#   ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
# KQ := PathAlgebra(GF(2), Q);
# beta := GeneratorsOfAlgebra(KQ)[4];
# delta := GeneratorsOfAlgebra(KQ)[5];
# eta := GeneratorsOfAlgebra(KQ)[6];
# gamma := GeneratorsOfAlgebra(KQ)[7];
# I := Ideal(KQ, [beta*gamma, eta*delta, beta*delta*eta*gamma, delta*eta*gamma*beta,
#     eta*gamma*beta*delta, gamma*beta*delta*eta]);

String2Txt := function(C)
    return String(List(C, x -> [x[1], WalkOfPathOrVertex(x[2])]));
end;


# returns a list of all strings of the form a*str and str*a, where a is an arrow or an inverse of an arrow.
# (this is used for the purpose of recursively enumerating all strings up to a given length)
ExtendString := function(KQ, I, str)
    local m, ext, ret, a, ar;
    ar := ArrowsOfQuiver(QuiverOfPathAlgebra(KQ));
    m := Size(str);
    ret := [ ];
    if str[m][1] = "D" then
        # Make intermediate point (reverse direction)
        if LengthOfPath(str[m][2]) > 0 then
            for a in ar do
                if TargetOfPath(a) = TargetOfPath(str[m][2]) and
                        a <> Reversed(WalkOfPath(str[m][2]))[1] then
                    Add(ret, Concatenation(str, [["I", a]]));
                fi;
            od;
        fi;
        # Extend current path
        for a in ar do
            if not ElementOfPathAlgebra(KQ, str[m][2]*a) in I then
                Add(ret, Concatenation(str{[1..m-1]}, [["D", str[m][2]*a]]));
            fi;
        od;
    fi;
    if str[m][1] = "I" then
        # Make intermediate point (reverse direction)
        if LengthOfPath(str[m][2]) > 0 then
            for a in ar do
                if SourceOfPath(a) = SourceOfPath(str[m][2]) and a <> WalkOfPath(str[m][2])[1] then
                    Add(ret, Concatenation(str, [["D", a]]));
                fi;
            od;
        fi;
        # Extend current path
        for a in ar do
            if not ElementOfPathAlgebra(KQ, a*str[m][2]) in I then
                Add(ret, Concatenation(str{[1..m-1]}, [["I", a*str[m][2]]]));
            fi;
        od;
    fi;
    return ret;
end;

# Compute all string over KQ/I up to length n
AllStringMaxLength := function(KQ, I, n)
    local layer, layer2, res, i;
    layer := Concatenation(List(VerticesOfQuiver(QuiverOfPathAlgebra(KQ)), v -> [[["D", v]], [["I", v]]]));
    res := [ layer ];
    for i in [1..n] do
        layer2 := Concatenation(List(layer, str -> ExtendString(KQ, I, str)));
        Add(res, layer2);
        layer := layer2;
    od;
    return Concatenation(res);
end;

# Compute str^(-1)
InverseOfString := function(str)
    local str2, i;
    str2 := StructuralCopy(Reversed(str));
    for i in [1..Size(str2)] do
        if str2[i][1] = "D" then
            str2[i][1] := "I";
        else
            str2[i][1] := "D";
        fi;
    od;
    return str2;
end;

# Given a list of strings, returns a list in which each string corresponds to a *different* string module
RemoveDuplicateStrings := function(lst)
    local ret, str, str2;
    ret := [ ];
    for str in lst do
        if String2Txt(str) in List(ret, String2Txt) or String2Txt(InverseOfString(str)) in List(ret, String2Txt) then
            continue;
        fi;
        str2 := StructuralCopy(str);
        if str2[1][1] = "I" and str2[Size(str2)][1] = "I" then
            str2 := InverseOfString(str2);
        fi;
        Add(ret, str2);
    od;
    return ret;
end;

# check whether path is a loose end (on the right)
IsLooseEnd := function(KQ, I, path)
    local ar;
    ar := ArrowsOfQuiver(QuiverOfPathAlgebra(KQ));
    return ForAll(ar, a -> ElementOfPathAlgebra(KQ, path*a) in I);
end;

# Compute _PC_P, where C=str_ and KQ/I is a string algebra
ProjectiveString := function(KQ, I, str_)
    local ar, a, ext, Pstr, PstrP, str;
    str := StructuralCopy(str_);
    ar := ArrowsOfQuiver(QuiverOfPathAlgebra(KQ));
    # Vertices are special
    if Size(str) = 1 and LengthOfPath(str[1][2])=0 then
        ext := Filtered(ar, a -> SourceOfPath(a) = str[1][2]);
        if Size(ext) = 0 then return str; fi;
        if Size(ext) = 1 then return [["D", ext[1]]]; fi;
        if Size(ext) = 2 then return [["I", ext[1]], ["D", ext[2]]]; fi;
        Error("WTF?");
    fi;

    # Length one may be special if the string is just a loose end:
    if Size(str) = 1 and IsLooseEnd(KQ, I, str[1][2]) then
        ext := Filtered(ar, a -> SourceOfPath(a) = SourceOfPath(str[1][2]) and
            a <> WalkOfPath(str[1][2])[1]);
        if Size(ext) = 0 then
            return [["D", SourceOfPath(str[1][2])]];
        fi;
        if Size(ext) = 1 then
            return [["D", ext[1]]];
        fi;
        Error("WTF?");
    fi;

    # Length > 1 (and length 1 without loose ends)
    if str[1][1] = "I" then
        if IsLooseEnd(KQ, I, str[1][2]) then
            Pstr := str{[2..Size(str)]};
        else
            Pstr := str;
            Pstr[1][2] := Filtered(List(ar, a -> str[1][2]*a), v -> not ElementOfPathAlgebra(KQ, v) in I)[1];
        fi;
    fi;
    if str[1][1] = "D" then
        ext := Filtered(ar, a -> SourceOfPath(a) = SourceOfPath(str[1][2]) and
            a <> WalkOfPath(str[1][2])[1]);
        if Size(ext) = 0 then
            Pstr := str;
        else
            Pstr := Concatenation([["I", ext[1]]], str);
        fi;
    fi;

    if Pstr[Size(Pstr)][1] = "D" then
        if IsLooseEnd(KQ, I, Pstr[Size(Pstr)][2]) then
            if Size(Pstr) = 1 then
                PstrP := [["D", SourceOfPath(Pstr[1][2])]];
            else
                PstrP := Pstr{[1..Size(Pstr)-1]};
            fi;
        else
            PstrP := Pstr;
            PstrP[Size(Pstr)][2] := Filtered(List(ar, a -> Pstr[Size(Pstr)][2]*a),
                v -> not ElementOfPathAlgebra(KQ, v) in I)[1];
        fi;
    fi;
    if Pstr[Size(Pstr)][1] = "I" then
        ext := Filtered(ar, a -> SourceOfPath(a) = SourceOfPath(Pstr[Size(Pstr)][2]) and
            a <> WalkOfPath(Pstr[Size(Pstr)][2])[1]);
        if Size(ext) = 0 then
            PstrP := Pstr;
        else
            PstrP := Concatenation(str, [["D", ext[1]]]);
        fi;
    fi;

    return PstrP;
end;


# Part of the definition of being C-presilted
CheckCommonSubstringCondition := function(KQ, I, C, D)
  local C_, C0, D_, IPC_, IPD_, i, j, sgn, ori, i_, j_, cond;
  C_ := ProjectiveString(KQ, I, C);
  if C_[1][1] = "D" then
    IPC_ := [["U", SourceOfPath(C_[1][2])]];
  fi;
  if C_[1][1] = "I" then
    IPC_ := [["L", TargetOfPath(C_[1][2])]];
  fi;
  if Size(C_) = 1 and LengthOfPath(C_[1][2]) = 0 then
    IPC_ := [["U", SourceOfPath(C_[1][2])]];
  else
    for i in [1..Size(C_)] do
      Add(IPC_, C_[i]);
      if C_[i][1] = "D" then
	        Add(IPC_, ["L", TargetOfPath(C_[i][2])]);
      else
	        Add(IPC_, ["U", SourceOfPath(C_[i][2])]);
      fi;
    od;
  fi;

  D_ := ProjectiveString(KQ, I, D);
  if D_[1][1] = "D" then
    IPD_ := [["U", SourceOfPath(D_[1][2])]];
  fi;
  if D_[1][1] = "I" then
    IPD_ := [["L", TargetOfPath(D_[1][2])]];
  fi;
  if Size(D_) = 1 and LengthOfPath(D_[1][2]) = 0 then
    IPD_ := [["U", SourceOfPath(D_[1][2])]];
  else
    for i in [1..Size(D_)] do
      Add(IPD_, D_[i]);
      if D_[i][1] = "D" then
	        Add(IPD_, ["L", TargetOfPath(D_[i][2])]);
      else
	        Add(IPD_, ["U", SourceOfPath(D_[i][2])]);
      fi;
    od;
  fi;


  for i in [1.. Size(IPC_)] do
    for j in [1..Size(IPD_)] do
      if IPC_[i][1] = IPD_[j][1] and IPC_[i][2] = IPD_[j][2] and IPC_[i][1] in ["L", "U"] then
	    ori := 1;
	    if i < Size(IPC_) and j > 1 then
	        if IPC_[i][1] = "U" then
	            if WalkOfPath(IPC_[i+1][2])[1] = WalkOfPath(IPD_[j-1][2])[1] then
	                ori := -1;
	             fi;
	        else
	            if Reversed(WalkOfPath(IPC_[i+1][2]))[1] = Reversed(WalkOfPath(IPD_[j-1][2]))[1] then
	                ori := -1;
	            fi;
	        fi;
	    elif i > 1 and j < Size(IPD_) then
	        if IPC_[i][1] = "U" then
	            if WalkOfPath(IPC_[i-1][2])[1] = WalkOfPath(IPD_[j+1][2])[1] then
	                ori := -1;
	            fi;
	        else
	            if Reversed(WalkOfPath(IPC_[i-1][2]))[1] = Reversed(WalkOfPath(IPD_[j+1][2]))[1] then
	                ori := -1;
	            fi;
	        fi;
	    fi;

	    cond := false;
	    for sgn in [1,-1] do
	        i_ := i;  j_ := j;
	        while true do
	            if i_ + 2*sgn > Size(IPC_) or  i_ + 2*sgn <= 0 then
	                break;
	            fi;
	            if j_ + 2*sgn*ori > Size(IPD_) or  j_ + 2*sgn*ori <= 0 then
	                break;
	            fi;
	            if IPC_[i_ + sgn][2] <> IPD_[j_ + sgn*ori][2] then
	                break;
	            fi;
	            i_ := i_ + 2*sgn; j_ := j_ + 2*sgn*ori;
	        od;

	        if IPC_[i_][1] = "U" then
	            if (i_ + 2*sgn <= 0) or (i_ + 2*sgn > Size(IPC_)) then
	                cond := true; # C'_{i_+1} does not exist
	            else
	                if (j_ + 2*sgn*ori > 0) and (j_ + 2*sgn*ori <= Size(IPD_)) then
		                if LengthOfPath(IPC_[i_+sgn][2]) > LengthOfPath(IPD_[j_+sgn*ori][2]) then
		                    cond := true;
		                fi;
	                fi;
	            fi;
	        else
	            if (j_ + 2*sgn*ori <= 0) or (j_ + 2*sgn*ori > Size(IPD_)) then
	                cond := true; # D'_{j_+1} does not exist
	            else
	                if (i_ + 2*sgn > 0) and (i_ + 2*sgn <= Size(IPC_)) then
		                if LengthOfPath(IPC_[i_+sgn][2]) < LengthOfPath(IPD_[j_+sgn*ori][2]) then
		                    cond := true;
		                fi;
	                fi;
	            fi;
	        fi;
	    od;
	    if not cond then
	        return false;
	    fi;
     fi;
    od;
  od;
  return true;
end;

# Check if D is C-presilted
CheckRelativeRigidness := function(KQ, I, C, D)
    local C_, D_, i, j, adjC, adjD, eD, eC, paths, p, a, factors, A, adjCidx, adjDidx;

    if not CheckCommonSubstringCondition(KQ, I, C, D) then
      return false;
    fi;

    A := KQ/I;
    paths := AsSet(Concatenation(List(Basis(A), b -> List(PathAlgebraElementTerms(b), v -> v.monom))));
    C_ := ProjectiveString(KQ, I, C);
    if Size(C_) = 1 and LengthOfPath(C_[1][2]) = 0 then
           return true; # C projective (doesn't have lower intermediate points)
    fi;
    D_ := ProjectiveString(KQ, I, D);
    for i in [0..Size(C_)] do
        if i mod 2 = 1 and C_[1][1] = "I" or i mod 2 = 0 and C_[1][1] = "D" then
            continue; # not a lower intermediate point
        fi;
        adjCidx := Filtered([i, i+1], n -> n > 0 and n <= Size(C_));
        adjC := List(C_{Filtered([i, i+1], n -> n > 0 and n <= Size(C_))}, x -> x[2]);
        eC := TargetOfPath(adjC[1]);
        for j in [0..Size(D_)] do
            if j mod 2 = 1 and D_[1][1] = "D" or j mod 2 = 0 and D_[1][1] = "I" then
                continue; # not an upper intermediate point
            fi;
            adjDidx := Filtered([j, j+1], n -> n > 0 and n <= Size(D_));
            adjD := List(D_{Filtered([j, j+1], n -> n > 0 and n <= Size(D_))}, x -> x[2]);
            if Size(D_) = 1 and LengthOfPath(D_[1][2]) = 0 then
                eD := D_[1][2];
            else
                eD := SourceOfPath(adjD[1]);
            fi;
            adjD := Filtered(adjD, x -> LengthOfPath(x) > 0);
            adjDidx := Filtered(adjDidx, x -> LengthOfPath(D_[x][2]) > 0);

            # Check rigidness condition
            for p in paths do
                factors := false;
                if SourceOfPath(p) <> eD or TargetOfPath(p) <> eC then
                    continue;
                fi;
                for a in [1..Size(adjD)] do
                    if LengthOfPath(p) >= LengthOfPath(adjD[a]) then
                        if String(WalkOfPath(p){[1..LengthOfPath(adjD[a])]}) = String(WalkOfPath(adjD[a])) then
                            factors := true;
                        fi;
                    fi;
                od;
                for a in [1..Size(adjC)] do
                    if LengthOfPath(p) >= LengthOfPath(adjC[a]) then
                        if String(Reversed(WalkOfPath(p)){[1..LengthOfPath(adjC[a])]})
                                    = String(Reversed(WalkOfPath(adjC[a]))) then
			                factors := true;
                        fi;
                    fi;
                od;
                if not factors then
                    return [i, j, eC, eD, p];
                fi;
            od;
        od;
    od;
    return true;
end;

CheckSupportOrthogonality := function(KQ, I, C, e)
    local C_, i, j, adjC, adjD, eD, eC, paths, p, a, factors, A;
    A := KQ/I;
    paths := AsSet(Concatenation(List(Basis(A), b -> List(PathAlgebraElementTerms(b), v -> v.monom))));
    C_ := ProjectiveString(KQ, I, C);
    for i in [0..Size(C_)] do
        if i mod 2 = 1 and C_[1][1] = "D" or i mod 2 = 0 and C_[1][1] = "I" then
            adjC := List(C_{Filtered([i, i+1], n -> n > 0 and n <= Size(C_))}, x -> x[2]);
            eC := TargetOfPath(adjC[1]);
            if Size(C_) = 1 and LengthOfPath(C_[1][2]) = 0 then
                adjC := [ ];
            fi;
            if e = eC and Size(adjC) = 2 then
                return false; # interior condition not met
            fi;
            continue; # not an upper intermediate point
        fi;
        adjC := List(C_{Filtered([i, i+1], n -> n > 0 and n <= Size(C_))}, x -> x[2]);
        eC := SourceOfPath(adjC[1]);
        if Size(C_) = 1 and LengthOfPath(C_[1][2]) = 0 then
            adjC := [ ];
        fi;

        # Check rigidness condition
        for p in paths do
            factors := false;
            if SourceOfPath(p) <> eC or TargetOfPath(p) <> e then
                continue;
            fi;
            for a in adjC do
                if LengthOfPath(p) >= LengthOfPath(a) then
                    if String(WalkOfPath(p){[1..LengthOfPath(a)]}) = String(WalkOfPath(a)) then
                        factors := true;
                    fi;
                fi;
            od;
            if not factors then
                return [i, eC, p];
            fi;
        od;
    od;
    return true;
end;

# Compute the g-vector of the string C over the string algebra KQ/I
GVectorOfString := function(KQ, I, C)
    local C_, v, sgn, i, vx;
    vx := VerticesOfQuiver(QuiverOfPathAlgebra(KQ));
    C_ := ProjectiveString(KQ, I, C);
    v := NullMat(2, Size(VerticesOfQuiver(QuiverOfPathAlgebra(KQ))));
    if Size(C_) = 1 and LengthOfPath(C_[1][2]) = 0 then
        v[1][Position(vx, C_[1][2])] := 1;
        return v[1]-v[2];
    fi;
    if C_[1][1] = "I" then
        sgn := 0;
        v[2][Position(vx, TargetOfPath(C_[1][2]))] := 1;
    else
        sgn := 1;
        v[1][Position(vx, SourceOfPath(C_[1][2]))] := 1;
    fi;
    for i in [1..Size(C_)] do
        if i mod 2 + sgn = 1 then
            v[1][Position(vx, SourceOfPath(C_[i][2]))] := v[1][Position(vx, SourceOfPath(C_[i][2]))] + 1;
        else
            v[2][Position(vx, TargetOfPath(C_[i][2]))] := v[2][Position(vx, TargetOfPath(C_[i][2]))] + 1;
        fi;
    od;
    return v[1]-v[2];
end;

############################################################################################################
# Functions which produce LaTeX output (very specific to our paper)

String2Latex := function(C)
    local ret, c, hom;
    if C[1][1] = "D" then
        ret := String(SourceOfPath(C[1][2]));
    else
        ret := String(TargetOfPath(C[1][2]));
    fi;
    if Size(C) = 1 and LengthOfPath(C[1][2]) = 0 then
        return ret;
    fi;
    for c in C do
        hom := Concatenation(List(WalkOfPath(c[2]), String));
        if c[1] = "D" then
            ret := Concatenation(ret, "\\stackrel{", hom, "}{\\longrightarrow}", String(TargetOfPath(c[2])));
        else
            ret := Concatenation(ret, "\\stackrel{", hom, "}{\\longleftarrow}", String(SourceOfPath(c[2])));
        fi;
    od;
    return ret;
end;

MakeRigidTableForAlg := function(KQ, I, max)
    local rigids, C, D, ret, rel, rel2, highlight, lst, i, dict, Name, Idx, Comp, vx;

    dict := [[[1,0,0], "P_0"], [[0,1,0], "P_1"], [[0,0,1], "P_2"],
        [[-1,0,0], "P_0^\\vee"], [[0,-1,0], "P_1^\\vee"], [[0,0,-1], "P_2^\\vee"],
        [[1,-1,-1], "X"], [[-1, 1, 1], "X^\\vee"],
        [[1,-1,0], "M_2"], [[-1,1,0], "M_2^\\vee"],
        [[1,0,-1], "M_1"], [[-1,0,1], "M_1^\\vee"],
        [[0,1,-1], "M_0"], [[0,-1,1], "M_0^\\vee"],
        [[1,0,-2], "T_1"], [[-1,0,2], "T_1^\\vee"],
        [[1,-2,0], "T_2"], [[-1,2,0], "T_2^\\vee"],
        [[1,-1,1], "Y"], [[-1,1,-1], "Y^\\vee"],
        [[1,1,-1], "Z"], [[-1,-1,1], "Z^\\vee"],

        [[1,0], "P_0"], [[0,1], "P_1"],
        [[-1,0], "P_0^\\vee"], [[0,-1], "P_1^\\vee"],
        [[1,-2], "X"], [[-1,2], "X^\\vee"],
        [[1,-1], "Y"], [[-1,1], "Y^\\vee"] ];

    Name := function(gv)
        local d;
        d := Filtered(dict, v -> v[1] = gv);
        if Size(d) > 0 then return d[1][2]; else return String(gv); fi;
    end;

    Idx := function(gv)
        local d;
        d := Filtered([1..Size(dict)], v -> dict[v][1] = GVectorOfString(KQ, I, gv));
        if Size(d) > 0 then return d[1]; else return 100000; fi;
    end;

    Comp := function(gv1, gv2)
        return Idx(gv1) < Idx(gv2);
    end;

    ret := "";
    highlight := function(b)
        if b=true then return "\\mathbf"; else return ""; fi;
    end;
    rigids := Filtered(RemoveDuplicateStrings(AllStringMaxLength(KQ, I, 10)),
        C -> CheckRelativeRigidness(KQ, I, C, C)=true);
    Sort(rigids, Comp);

    vx := VerticesOfQuiver(QuiverOfPathAlgebra(KQ));

    for C in rigids do
        rel := Filtered(rigids, D -> CheckRelativeRigidness(KQ, I, C, D)=true);
        rel := List(rel, D -> [GVectorOfString(KQ, I, D), highlight(CheckRelativeRigidness(KQ, I, D, C))]);
        rel := Filtered(rel, r -> r[1] <> GVectorOfString(KQ, I, C));

        rel2 := Filtered([1..Size(vx)], e ->
            CheckSupportOrthogonality(KQ, I, C, vx[e])=true);
        rel2 := List(rel2, i -> [-IdentityMat(Size(vx))[i], "\\mathbf"]);

        rel := Concatenation(rel2, rel);

        lst := "";
        for i in [1..Size(rel)] do
            lst := Concatenation(lst, Concatenation("$", rel[i][2], "{",
                Name(rel[i][1]), "}$"));
            if i <> Size(rel) then lst := Concatenation(lst, ", "); fi;
        od;
        ret := Concatenation(ret, "$\\mathbf{", Name(GVectorOfString(KQ, I, C)), "}$ & $", String2Latex(C), "$ & $", String2Latex(ProjectiveString(KQ, I, C)), "$ & $",
            String(GVectorOfString(KQ, I, C)), "$ & ", lst ,"\\\\\n");
    od;
    return ret;
end;

MakeHead := function(name, out)
    PrintTo(out, "\\renewcommand\\arraystretch{1.5}\n\\tiny\\begin{longtable}{ccccc}\n");
	PrintTo(out, "\\Cline{1-5}{1.7pt}\n");
	PrintTo(out, "$\\mathbf{", name, "}$ & \\textbf{Rigid string $C$} & $_PC_P$ & \\textbf{$g$-vector} & \\textbf{Other $C$-rigid strings} \\\\\\Cline{1-5}{1.3pt} \\endhead\n");
	PrintTo(out, "\\Cline{1-5}{1.7pt} \\endfoot\n");
end;

MakeFoot := function(out)
    PrintTo(out, "\\end{longtable}\n");
end;

#############################################################################################
# Methods used for double-checking that the tau-rigid modules and presilting strings we
# are correct. Essentially, these are used for checking that the construction
# used in HasseQuiver(...) coincides with the purely combinatorial description using string.
# HasseQuiverCheck is useful for checking that the actual diagrams in our paper are correct.

SanityCheck := function(KQ, I)
    local A, rigidM, rigidS, gvM, gvS, ll, i, j, b1, b2;
    A := KQ/I;
    rigidM := Flat(HasseQuiver(A,100)[1]);
    gvM := List(rigidM, M -> DimensionVector(TopOfModule(M))-
        DimensionVector(TopOfModule(1stSyzygy(M))));
    ll := RemoveDuplicateStrings(AllStringMaxLength(KQ, I, 10));
    rigidS := Filtered(ll, str -> CheckRelativeRigidness(KQ, I, str, str)=true);
    gvS := List(rigidS, s -> GVectorOfString(KQ, I, s));
    if AsSet(gvS) <> AsSet(gvM) then
        Error("GVectors not the same!");
    fi;
    for i in [1..Size(gvS)] do
        for j in [1..Size(gvS)] do
            b1 := 0 = Size(HomOverAlgebra(rigidM[Position(gvM, gvS[i])], DTr(rigidM[Position(gvM, gvS[j])])));
            b2 := CheckRelativeRigidness(KQ, I, rigidS[j], rigidS[i]) = true;
            if b1 <> b2 then
                Error("Sanity check failed!");
            fi;
        od;
        # Check support
        for j in [1..Size(VerticesOfQuiver(QuiverOfPathAlgebra(KQ)))] do
            b1 := true = CheckSupportOrthogonality(KQ, I, rigidS[i], VerticesOfQuiver(QuiverOfPathAlgebra(KQ))[j]);
            b2 := DimensionVector(rigidM[Position(gvM, gvS[i])])[j] = 0;
            if b1 <> b2 then
                Error("Sanity check failed (support)!");
            fi;
        od;
    od;
    Print("Sanity check passed!\n");
end;

HasseQuiverCheck := function(KQ, I, out)
    local q, dict, Name,  v, w;

    dict := [[[1,0,0], "P_0"], [[0,1,0], "P_1"], [[0,0,1], "P_2"],
        [[-1,0,0], "P_0^\\vee"], [[0,-1,0], "P_1^\\vee"], [[0,0,-1], "P_2^\\vee"],
        [[1,-1,-1], "X"], [[-1, 1, 1], "X^\\vee"],
        [[1,-1,0], "M_2"], [[-1,1,0], "M_2^\\vee"],
        [[1,0,-1], "M_1"], [[-1,0,1], "M_1^\\vee"],
        [[0,1,-1], "M_0"], [[0,-1,1], "M_0^\\vee"],
        [[1,0,-2], "T_1"], [[-1,0,2], "T_1^\\vee"],
        [[1,-2,0], "T_2"], [[-1,2,0], "T_2^\\vee"],
        [[1,-1,1], "Y"], [[-1,1,-1], "Y^\\vee"],
        [[1,1,-1], "Z"], [[-1,-1,1], "Z^\\vee"],

        [[1,0], "P_0"], [[0,1], "P_1"],
        [[-1,0], "P_0^\\vee"], [[0,-1], "P_1^\\vee"],
        [[1,-2], "X"], [[-1,2], "X^\\vee"],
        [[1,-1], "Y"], [[-1,1], "Y^\\vee"] ];

    Name := function(gv)
        local d;
        d := Filtered(dict, v -> v[1] = gv);
        if Size(d) > 0 then return d[1][2]; else return String(gv); fi;
    end;

    q := HasseQuiver(KQ/I, 100)[1];
    q := List(q, v -> List(v, M -> DimensionVector(TopOfModule(M))-
        DimensionVector(TopOfModule(1stSyzygy(M)))));
    q := List(q, v -> List(v, Name));
    for v in q do
        PrintTo(out, "$ ");
        for w in v do
            PrintTo(out, w);
            if Position(v, w) <> Size(v) then
                PrintTo(out, " \\oplus ");
            fi;
        od;
        PrintTo(out, "$, ");
    od;
end;

##############################################################################
# Function that creates the tables of presilting strings in the paper

MakeRigidTable := function(fname)
    local Q, beta, delta, eta, gamma, lambda, kappa, alpha, KQ, I, name, out, check, check2;

    check := false;
    check2 := false;
    out := OutputTextFile(fname, false);
    SetPrintFormattingStatus(out, false);

    # R2(AB)
    name := "R(2AB)";
    Q := Quiver(["0","1"], [["0", "1", "\\beta"],  ["1", "0", "\\gamma"],
        ["0", "0", "\\alpha"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[3];
    gamma := GeneratorsOfAlgebra(KQ)[4];
    alpha := GeneratorsOfAlgebra(KQ)[5];
    I := Ideal(KQ, [beta*gamma, gamma*beta, alpha^2, gamma*alpha*beta]);
    # Display(List(Basis(KQ/I)));
    PrintTo(out, "\\newcommand{\\RtwoAB}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # W2(B)
    name := "W(2B)";
    Q := Quiver(["0","1"], [["0", "1", "\\beta"],  ["1", "0", "\\gamma"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[3];
    gamma := GeneratorsOfAlgebra(KQ)[4];
    I := Ideal(KQ, [beta*gamma, gamma*beta]);
    PrintTo(out, "\\newcommand{\\WtwoB}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;


    # R3(ABD)
    name := "R(3ABD)";
    Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
  ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    I := Ideal(KQ, [beta*gamma, eta*delta, beta*delta*eta*gamma, delta*eta*gamma*beta,
    eta*gamma*beta*delta, gamma*beta*delta*eta]);
    PrintTo(out, "\\newcommand{\\RthreeABD}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # R3(C)
    name := "R(3C)";
    Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
  ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    I := Ideal(KQ, [beta*gamma, eta*delta, gamma*beta, delta*eta]);
    PrintTo(out, "\\newcommand{\\RthreeC}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # R3(H)
    name := "R(3H)";
    Q := Quiver(["0","1","2"], [["0", "1", "\\beta"], ["1", "2", "\\delta"],
  ["2", "1", "\\eta"], ["1", "0", "\\gamma"], ["2", "0", "\\lambda"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    lambda := GeneratorsOfAlgebra(KQ)[8];
    I := Ideal(KQ, [delta*lambda, lambda*beta, eta*delta, delta*eta,
        beta*gamma, gamma*beta, eta*gamma]);
    PrintTo(out, "\\newcommand{\\RthreeH}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # R3(K)
    name := "R(3K)";
    Q := Quiver(["0","1","2"], [["0", "1", "\\beta"], ["1", "2", "\\delta"],
  ["2", "1", "\\eta"], ["1", "0", "\\gamma"], ["2", "0", "\\lambda"], ["0", "2", "\\kappa"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    lambda := GeneratorsOfAlgebra(KQ)[8];
    kappa := GeneratorsOfAlgebra(KQ)[9];
    I := Ideal(KQ, [beta*delta, delta*lambda, lambda*beta,
        gamma*kappa, kappa*eta, eta*gamma, beta*gamma, gamma*beta,
        lambda*kappa, kappa*lambda, delta*eta, eta*delta]);
    PrintTo(out, "\\newcommand{\\RthreeK}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # W3(ABCD)
    name := "W(3ABCD)";
    Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
  ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    I := Ideal(KQ, [beta*gamma, gamma*beta, delta*eta, eta*delta, beta*delta, eta*gamma]);
    PrintTo(out, "\\newcommand{\\WthreeABCD}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

     # W(Q3A1)
    name := "W(Q(3A)_1)";
    Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
  ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    gamma := GeneratorsOfAlgebra(KQ)[7];
    I := Ideal(KQ, [beta*gamma, gamma*beta, delta*eta, eta*delta, beta*delta*eta,
        delta*eta*gamma, gamma*beta*delta, eta*gamma*beta]);
    PrintTo(out, "\\newcommand{\\WthreeQA}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # W3(F)
    name := "W(3F)";
    Q := Quiver(["0","1","2"], [["0", "1", "\\beta"], ["1", "2", "\\delta"],
  ["2", "1", "\\eta"], ["2", "0", "\\lambda"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    eta := GeneratorsOfAlgebra(KQ)[6];
    lambda := GeneratorsOfAlgebra(KQ)[7];
    I := Ideal(KQ, [delta*eta, eta*delta, lambda*beta, beta*delta*lambda,
        delta*lambda*beta, lambda*beta*delta]);
    PrintTo(out, "\\newcommand{\\WthreeF}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    # W3(QLR)
    name := "W(3QLR)";
    Q := Quiver(["0","1","2"], [["0", "1", "\\beta"], ["1", "2", "\\delta"],
     ["2", "0", "\\lambda"]]);
    KQ := PathAlgebra(GF(2), Q);
    beta := GeneratorsOfAlgebra(KQ)[4];
    delta := GeneratorsOfAlgebra(KQ)[5];
    lambda := GeneratorsOfAlgebra(KQ)[6];
    I := Ideal(KQ, [beta*delta*lambda,
        delta*lambda*beta, lambda*beta*delta]);
    PrintTo(out, "\\newcommand{\\WthreeQLR}{");
    MakeHead(name, out);
    PrintTo(out, MakeRigidTableForAlg(KQ, I, 10));
    MakeFoot(out);
    if check2 then HasseQuiverCheck(KQ, I, out); fi;
    PrintTo(out, "}\n");
    if check then Print("Checking ", name, "\n"); SanityCheck(KQ, I); fi;

    CloseStream(out);
end;

#     Q := Quiver(["0","1","2"], [["1", "0", "\\beta"], ["0", "2", "\\delta"],
#   ["2", "0", "\\eta"], ["0", "1", "\\gamma"]]);
#     KQ := PathAlgebra(GF(2), Q);
#     beta := GeneratorsOfAlgebra(KQ)[4];
#     delta := GeneratorsOfAlgebra(KQ)[5];
#     eta := GeneratorsOfAlgebra(KQ)[6];
#     gamma := GeneratorsOfAlgebra(KQ)[7];
#     I := Ideal(KQ, [beta*gamma, eta*delta, beta*delta*eta*gamma, delta*eta*gamma*beta,
#     eta*gamma*beta*delta, gamma*beta*delta*eta]);
#    ll := RemoveDuplicateStrings(AllStringMaxLength(KQ, I, 10));
#     rigid := Filtered(ll, str -> CheckRelativeRigidness(KQ, I, str, str)=true);
#     # T1 := rigid[6];
#     # M1 := rigid[8];
#      XX := [["D", VerticesOfQuiver(Q)[1]]];
#


###############################################################################
# Graded algebras and generalized separated quivers (was used for an earlier approach
# to the problem considered in our paper; loosely related to Adachi's paper on
# hereditary algebras.

Res := function(A, M)
    local As, K, Q, Qs, n, dimv, a, arQs, vxQs, matsAs, matsa, v0, v1, idx,
        mat, ret_mat, x1, y1, x0, y0, x, y, i;
    As := RightActingAlgebra(M);
    K := LeftActingDomain(M);
    Q := QuiverOfPathAlgebra(A);
    Qs := QuiverOfPathAlgebra(As);
    n := Size(VerticesOfQuiver(Qs))/Size(VerticesOfQuiver(Q));
    arQs := List(ArrowsOfQuiver(Qs), String);
    vxQs := List(VerticesOfQuiver(Qs), String);
    matsAs := MatricesOfPathAlgebraModule(M);
    ret_mat := [];
    dimv := List(VerticesOfQuiver(Q), v -> Sum(List([1..n], i ->
        DimensionVector(M)[Position(vxQs, Concatenation(String(v), "_",
        String(i)))])));
    for a in ArrowsOfQuiver(Q) do
        matsa := List([1..n-1], i ->
            matsAs[Position(arQs, Concatenation(String(a), "_", String(i)))]);
        v0 := String(SourceOfPath(a));
        v1 := String(TargetOfPath(a));
        if dimv[Position(List(VerticesOfQuiver(Q), String), v0)] = 0 or
            dimv[Position(List(VerticesOfQuiver(Q), String), v1)] = 0 then
                continue;
        fi;
        mat := One(K)*NullMat(dimv[Position(List(VerticesOfQuiver(Q), String), v0)],
            dimv[Position(List(VerticesOfQuiver(Q), String), v1)], K);
        x0 := 1;
        y0 := 1;
        for i in [1..n-1] do
            y0 := y0 + DimensionVector(M)[Position(vxQs, Concatenation(v1, "_", String(i)))];
            if DimensionVector(M)[Position(vxQs,
                Concatenation(v0, "_", String(i)))] <> 0 and
                DimensionVector(M)[Position(vxQs,
                Concatenation(v0, "_", String(i+1)))] <> 0 then

                    x1 := Size(matsa[i]);
                    y1 := Size(matsa[i][1]);
                    for x in [0..x1-1] do
                        for y in [0..y1-1] do
                            mat[x0+x][y0+y] := matsa[i][1+x][1+y];
                        od;
                    od;

            fi;
            x0 := x0 + DimensionVector(M)[Position(vxQs, Concatenation(v0, "_", String(i)))];
        od;
        Add(ret_mat, [String(a), mat]);
    od;
    return RightModuleOverPathAlgebra(A, dimv, ret_mat);
end;

SingleSubquiversSS := function(Q)
    # Find all "single" subquivers of the separated quiver of Q
    local V, V_, SS, subsets, idx, vx, QS, lst;
    V := List(VerticesOfQuiver(Q), String);
    V_ := List(V, x -> Concatenation(x, "'"));
    SS := SeparatedQuiver(Q);
    subsets := Combinations([1..Size(V)]);
    lst := [];
    for idx in subsets do
        vx := Concatenation(V{idx}, V_{Filtered([1..Size(V)],
            x -> not x in idx)});
        QS := FullSubquiver(SS, Filtered(VerticesOfQuiver(SS),
            vv -> String(vv) in vx));
        Append(lst, ConnectedComponentsOfQuiver(QS));
    od;
    return lst;
end;

ExpandRep := function(kQ, M)
    # Expand the module M defined over e*kQ*e to kQ
    # (kQ may not have any relations and must be finite dimensional)
    local kQs, Qsnames, dims, dim, lst, a, Qsarnames, Qnames, ars, ddims, pos,
          mat, F;

    F := LeftActingDomain(kQ);
    kQs := RightActingAlgebra(M);
    Qsnames := List(VerticesOfQuiver(QuiverOfPathAlgebra(kQs)), String);
    Qsarnames := List(ArrowsOfQuiver(QuiverOfPathAlgebra(kQs)), String);
    Qnames := List(VerticesOfQuiver(QuiverOfPathAlgebra(kQ)), String);
    dims := DimensionVector(M);
    dim := List(VerticesOfQuiver(QuiverOfPathAlgebra(kQ)), function(v)
        if String(v) in Qsnames then
            return dims[Position(Qsnames, String(v))];
        else
            return Sum(List(Filtered(List(IncomingArrowsOfVertex(v),
                a -> String(SourceOfPath(a))), s -> s in Qsnames),
                x -> dims[Position(Qsnames, x)]));
        fi; end
    );
    lst := [];
    for a in ArrowsOfQuiver(QuiverOfPathAlgebra(kQ)) do
        if dim[Position(Qnames, String(SourceOfPath(a)))] = 0
                or dim[Position(Qnames, String(TargetOfPath(a)))] = 0 then
            continue;
        fi;
        if String(a) in Qsarnames then
            Add(lst, [String(a),
                MatricesOfPathAlgebraModule(M)[Position(Qsarnames,
                String(a))]]);
        elif String(SourceOfPath(a)) in Qsnames then
            ars := Filtered(ArrowsOfQuiver(QuiverOfPathAlgebra(kQ)),
                b -> TargetOfPath(b) = TargetOfPath(a)
                and String(SourceOfPath(b)) in Qsnames);
            ddims := List(ars, b -> dims[Position(Qsnames,
                String(SourceOfPath(b)))]);
            pos := Position(ars, a);
            mat := One(F) * IdentityMat(Sum(ddims)){
                [Sum(ddims{[1..pos-1]})+1..Sum(ddims{[1..pos]})]};
            Add(lst, [String(a), mat]);
        else
            Add(lst, [String(a), One(F) * NullMat(
                dim[Position(Qnames, String(SourceOfPath(a)))],
                dim[Position(Qnames, String(TargetOfPath(a)))])]);
        fi;
    od;
    lst := Filtered(lst, v -> Size(v[2]) <> 0);
    return RightModuleOverPathAlgebra(kQ, dim, lst);
end;

CalculateFinv := function(kQ, M)
    # Takes a tau-rigid kQs-module M with conditions (see Theorem 3.2 in
    # Adachi's paper) and turns it into a tau-rigid kQ-module (rad^2(kQ) = 0)
    # Note: Qs is the separated quiver of Q.
    local kQs, Qnames, Qsnames, dims, dimt, dim, lst, ars, a, mat, idxs,
          idxt, i;
    kQs := RightActingAlgebra(M);
    Qnames := List(VerticesOfQuiver(QuiverOfPathAlgebra(kQ)), String);
    Qsnames := List(VerticesOfQuiver(QuiverOfPathAlgebra(kQs)), String);
    dims := List(Qnames, v -> 0);
    for i in [1..Size(Qnames)] do
        if Qnames[i] in Qsnames then
            dims[i] := DimensionVector(M)[Position(Qsnames, Qnames[i])];
        fi;
    od;
    dimt := List(Qnames, v -> 0);
    for i in [1..Size(Qnames)] do
        if Concatenation(Qnames[i], "'") in Qsnames then
            dimt[i] :=  DimensionVector(M)[Position(Qsnames,
                Concatenation(Qnames[i], "'"))];
        fi;
    od;
    dim := dims+dimt;
    lst := [];
    ars := List(ArrowsOfQuiver(QuiverOfPathAlgebra(kQ)), String);
    for a in List(ArrowsOfQuiver(QuiverOfPathAlgebra(kQs)), String) do
        mat := MatricesOfPathAlgebraModule(M)[
            Position(List(ArrowsOfQuiver(QuiverOfPathAlgebra(kQs)), String),
            a)];
        idxs := Position(Qnames, String(SourceOfPath(ArrowsOfQuiver(
            QuiverOfPathAlgebra(kQ))[Position(ars, a)])));
        idxt := Position(Qnames, String(TargetOfPath(ArrowsOfQuiver(
            QuiverOfPathAlgebra(kQ))[Position(ars, a)])));
        if dims[idxs] = 0 or dimt[idxt] = 0 then
            continue;
        fi;
        mat := List(IdentityMat(dim[idxs]), v -> v{[1..dims[idxs]]})*mat*
            IdentityMat(dim[idxt]){[dims[idxt]+1..dim[idxt]]};
        Add(lst, [a, mat]);
    od;
    return RightModuleOverPathAlgebra(kQ, dim, lst);
end;

nSeparatedQuiver := function(Q, n)
    local vertQ, vertQs, arQ, arQs;
    vertQ := List(VerticesOfQuiver(Q), String);
    arQ := ArrowsOfQuiver(Q);
    vertQs := Concatenation(List(vertQ, v -> List([1..n], i -> Concatenation(
        String(v), "_" , String(i)
    ))));
    arQs := Concatenation(List(arQ, a -> List([1..n-1], i ->
        [Concatenation(String(SourceOfPath(a)), "_", String(i)),
         Concatenation(String(TargetOfPath(a)), "_", String(i+1)),
         Concatenation(String(a), "_", String(i))
        ])));
    return Quiver(vertQs, arQs);
end;

## Maybe TODO: add relations!!!
nSeparatedAlgebra := function(A, n)
    return PathAlgebra(LeftActingDomain(A),
        nSeparatedQuiver(QuiverOfPathAlgebra(A), n));
end;

FunctorF := function(As, M) # Turn M into a As-module
    local A, K, Q, Qs, a, i, v, n, as, rad, map, src, tar, mat, mats, mm,
        dimv;
    A := RightActingAlgebra(M);
    K := LeftActingDomain(M);
    Q := QuiverOfPathAlgebra(A);
    Qs := QuiverOfPathAlgebra(As);
    n := Size(VerticesOfQuiver(Qs))/Size(VerticesOfQuiver(Q));
    rad := [[M, IdentityMapping(M), TopOfModuleProjection(M)]];
    for i in [1..n-1] do
        map := RadicalOfModuleInclusion(rad[Size(rad)][1]);
        Add(rad, [Source(map), map*rad[Size(rad)][2],
            TopOfModuleProjection(Source(map))]);
    od;

    for i in [1..n] do
        Add(rad[i], []);
        for v in VerticesOfQuiver(Q) do
            mm := List(Basis(Range(rad[i][3])), b -> b^(One(A)*v));
            if ForAll(mm, IsZero) then
                Add(rad[i][4], fail);
            else
                Add(rad[i][4], SubRepresentationInclusion(Range(rad[i][3]),
                    mm));
            fi;
        od;
    od;

    dimv := List(VerticesOfQuiver(Qs), String);
    for v in VerticesOfQuiver(Q) do
        for i in [1..n] do
            if i > Size(RadicalSeries(M)) then
                dimv[Position(dimv, Concatenation(String(v), "_", String(i)))] := 0;
                continue;
            fi;
            dimv[Position(dimv, Concatenation(String(v), "_", String(i)))] :=
                RadicalSeries(M)[i][Position(VerticesOfQuiver(Q), v)];
        od;
    od;

    mats := [];
    for a in ArrowsOfQuiver(Q) do
        for i in [1..n-1] do
            as := Concatenation(String(a), "_", String(i));
            src := rad[i][4][Position(VerticesOfQuiver(Q), SourceOfPath(a))];
            tar := rad[i+1][4][Position(VerticesOfQuiver(Q), TargetOfPath(a))];
            if src = fail or tar = fail then
                continue;
            fi;
            src := List(Basis(Source(src)), b -> ImageElm(rad[i][2],
                PreImagesRepresentative(rad[i][3], ImageElm(src, b))));
            mat := List(src, s -> Coefficients(Basis(Source(tar)),
                PreImagesRepresentative(tar, ImageElm(rad[i+1][3],
                PreImagesRepresentative(rad[i+1][2], s^(One(A)*a))))));
            Add(mats, [Concatenation(String(a), "_", String(i)), mat]);
        od;
    od;
    return RightModuleOverPathAlgebra(As, dimv, mats);
end;