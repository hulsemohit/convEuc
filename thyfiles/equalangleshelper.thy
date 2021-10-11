theory equalangleshelper
	imports Geometry ray3
begin

theorem(in euclidean_geometry) equalangleshelper:
	assumes 
		"ang_eq A B C a b c"
		"ray_on b a p"
		"ray_on b c q"
	shows "ang_eq A B C p b q"
proof -
	obtain U V u v where "ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C" using equalangles_f[OF `ang_eq A B C a b c`]  by  blast
	have "ray_on B A U" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on B C V" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b a u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b c v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B U b u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq B V b v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "seg_eq U V u v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "\<not> col A B C" using `ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
	have "ray_on b p u" using ray3[OF `ray_on b a p` `ray_on b a u`] .
	have "ray_on b q v" using ray3[OF `ray_on b c q` `ray_on b c v`] .
	have "ang_eq A B C p b q" using equalangles_b[OF `ray_on B A U` `ray_on B C V` `ray_on b p u` `ray_on b q v` `seg_eq B U b u` `seg_eq B V b v` `seg_eq U V u v` `\<not> col A B C`] .
	thus ?thesis by blast
qed

end