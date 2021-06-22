theory RTsymmetric
	imports Axioms Definitions Theorems
begin

theorem RTsymmetric:
	assumes: `axioms`
		"ang_suppl A B C D E F"
	shows: "ang_suppl D E F A B C"
proof -
	obtain a b c d e where "linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e" using tworightangles_f[OF `axioms` `ang_suppl A B C D E F`] by blast
	have "linear_pair a b c d e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq A B C a b c" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq D E F d b e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "linear_pair e b d c a" using supplementsymmetric[OF `axioms` `linear_pair a b c d e`] .
	have "\<not> col d b e" using equalanglesNC[OF `axioms` `ang_eq D E F d b e`] .
	have "ang_eq d b e e b d" using ABCequalsCBA[OF `axioms` `\<not> col d b e`] .
	have "\<not> col a b c" using equalanglesNC[OF `axioms` `ang_eq A B C a b c`] .
	have "ang_eq a b c c b a" using ABCequalsCBA[OF `axioms` `\<not> col a b c`] .
	have "ang_eq D E F e b d" using equalanglestransitive[OF `axioms` `ang_eq D E F d b e` `ang_eq d b e e b d`] .
	have "ang_eq A B C c b a" using equalanglestransitive[OF `axioms` `ang_eq A B C a b c` `ang_eq a b c c b a`] .
	have "ang_suppl D E F A B C" using tworightangles_b[OF `axioms` `linear_pair e b d c a` `ang_eq D E F e b d` `ang_eq A B C c b a`] .
	thus ?thesis by blast
qed

end