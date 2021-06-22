theory equalanglesreflexive
	imports Axioms Definitions Theorems
begin

theorem equalanglesreflexive:
	assumes: `axioms`
		"\<not> col A B C"
	shows: "ang_eq A B C A B C"
proof -
	have "ang_eq A B C C B A" using ABCequalsCBA[OF `axioms` `\<not> col A B C`] .
	have "\<not> col C B A" using equalanglesNC[OF `axioms` `ang_eq A B C C B A`] .
	have "ang_eq C B A A B C" using ABCequalsCBA[OF `axioms` `\<not> col C B A`] .
	have "ang_eq A B C A B C" using equalanglestransitive[OF `axioms` `ang_eq A B C C B A` `ang_eq C B A A B C`] .
	thus ?thesis by blast
qed

end