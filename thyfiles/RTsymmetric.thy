theory RTsymmetric
	imports ABCequalsCBA Geometry equalanglesNC equalanglestransitive supplementsymmetric
begin

theorem(in euclidean_geometry) RTsymmetric:
	assumes 
		"ang_sum_right A B C D E F"
	shows "ang_sum_right D E F A B C"
proof -
	obtain a b c d e where "supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e" using tworightangles_f[OF `ang_sum_right A B C D E F`]  by  blast
	have "supplement a b c d e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq A B C a b c" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq D E F d b e" using `supplement a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "supplement e b d c a" using supplementsymmetric[OF `supplement a b c d e`] .
	have "\<not> col d b e" using equalanglesNC[OF `ang_eq D E F d b e`] .
	have "ang_eq d b e e b d" using ABCequalsCBA[OF `\<not> col d b e`] .
	have "\<not> col a b c" using equalanglesNC[OF `ang_eq A B C a b c`] .
	have "ang_eq a b c c b a" using ABCequalsCBA[OF `\<not> col a b c`] .
	have "ang_eq D E F e b d" using equalanglestransitive[OF `ang_eq D E F d b e` `ang_eq d b e e b d`] .
	have "ang_eq A B C c b a" using equalanglestransitive[OF `ang_eq A B C a b c` `ang_eq a b c c b a`] .
	have "ang_sum_right D E F A B C" using tworightangles_b[OF `supplement e b d c a` `ang_eq D E F e b d` `ang_eq A B C c b a`] .
	thus ?thesis by blast
qed

end