type ('a, 'b) t

val make : ('a * 'b) list -> ('a, 'b) t
val to_list : ('a, 'b) t -> ('a * 'b) list
val equal : ('a, 'b) t -> ('a, 'b) t -> bool
val intersection : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
val restrict_diagonal : ('a, 'a) t -> ('a, 'a) t
