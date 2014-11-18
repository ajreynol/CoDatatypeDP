(*
    is_SCons (smap f (siterate id x)))
    siterate id (f x) = SCons (f x) (siterate id (id (f x)))
    smap id (siterate id (f x)) = siterate id (f x)
    shd (smap f (siterate id x)) = shd (siterate id (f x))
    f x = shd (siterate id (f x))
    stl (smap f (siterate id x)) = smap f (stl (siterate id x))
    stl (siterate id x) = siterate id (id x)
    smap id (siterate id x) = siterate id (id x)
    smap id (siterate id x) = siterate id x
    smap id (siterate id (f x)) = siterate id (id (f x))

      implies

    smap f (siterate id x) = smap id (siterate id (f x))
*)
