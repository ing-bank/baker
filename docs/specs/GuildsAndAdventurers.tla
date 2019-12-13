---------------------- MODULE InteractionManagerAgent ----------------------

CONSTANTS GUILDS, ADVENTURERS

VARIABLES guildsState, adventurersState

----------------------------------------------------------------------------

TypeOk == TRUE
    /\ guildsState \in [GUILDS -> UNION {{ <<"requesting", "">>, <<"completed", "">>, <<"committed", adv>>} : adv \in ADVENTURERS}]
    /\ adventurersState \in [ADVENTURERS -> UNION {{<<"looking-for-quest", "">>, <<"considering", guild>>, <<"committed", guild>>} : guild \in GUILDS}]

Init ==
    /\ guildsState = [guild \in GUILDS |-> <<"requesting", "">>]
    /\ adventurersState = [adventurers \in ADVENTURERS |-> <<"looking-for-quest", "">>]

AdventurerIsConsideringGuild(guild, adv) ==
    adventurersState[adv] = <<"considering", guild>>

AdventurerIsCommittedWithGuild(guild, adv) ==
    adventurersState[adv] = <<"committed", guild>>
    
GuildIsCommittedWithAdventurer(guild, adv) ==
    guildsState[guild] = <<"committed", adv>>
    
AreCommitted(guild, adv) ==
    /\ GuildIsCommittedWithAdventurer(guild, adv)
    /\ AdventurerIsCommittedWithGuild(guild, adv)

MatchExistsBetween(guild, adv) ==
    /\ guildsState[guild] = <<"requesting", "">>
    /\ adventurersState[adv] = <<"looking-for-quest", "">>
        
AdventurerIsReadyOk(guild, adv) ==
    /\ guildsState[guild] = <<"requesting", "">>
    /\ adventurersState[adv] = <<"considering", guild>>
    
GuildIsReadyOk(guild, adv) ==
    /\ guildsState[guild] = <<"committed", adv>>
    /\ adventurersState[adv] = <<"considering", guild>>
    
QuestInProgress(guild, adv) ==
    AreCommitted(guild, adv) 

QuestWasAlreadyTakenByAdv1(guild, adv1, adv2) ==
    /\ adv1 # adv2
    /\ ( guildsState[guild] = <<"committed", adv1>> \/ guildsState[guild] = <<"completed", "">> )
    /\ adventurersState[adv2] = <<"considering", guild>>
              
----------------------------------------------------------------------------    
    
AdventurerConsidersAQuest ==
    /\ \E <<guild, adv>> \in GUILDS \X ADVENTURERS : MatchExistsBetween(guild, adv)
    /\ LET guildAdv == CHOOSE <<guild, adv>> \in GUILDS \X ADVENTURERS : MatchExistsBetween(guild, adv)
           guild == guildAdv[1]
           adv == guildAdv[2]
       IN /\ adventurersState' = [adventurersState EXCEPT ![adv] = <<"considering", guild>>]
          /\ UNCHANGED guildsState

GuildCommitsToAnAdventurer ==
    /\ \E <<guild, adv>> \in GUILDS \X ADVENTURERS : AdventurerIsReadyOk(guild, adv)
    /\ LET guildAdv == CHOOSE <<guild, adv>> \in GUILDS \X ADVENTURERS : AdventurerIsReadyOk(guild, adv)
           guild == guildAdv[1]
           adv == guildAdv[2]
       IN /\ guildsState' = [guildsState EXCEPT ![guild] = <<"committed", adv>>]
          /\ UNCHANGED adventurersState

AdventurerCommitsToAGuild ==
    /\ \E <<guild, adv>> \in GUILDS \X ADVENTURERS : GuildIsReadyOk(guild, adv)
    /\ LET guildAdv == CHOOSE <<guild, adv>> \in GUILDS \X ADVENTURERS : GuildIsReadyOk(guild, adv)
           guild == guildAdv[1]
           adv == guildAdv[2]
       IN /\ adventurersState' = [adventurersState EXCEPT ![adv] = <<"committed", guild>>]
          /\ UNCHANGED guildsState

AdventurerDropsTakenQuest ==
    /\ \E <<guild, adv1, adv2>> \in GUILDS \X ADVENTURERS \X ADVENTURERS: QuestWasAlreadyTakenByAdv1(guild, adv1, adv2)
    /\ LET guildAdv == CHOOSE <<guild, adv1, adv2>> \in GUILDS \X ADVENTURERS \X ADVENTURERS :  QuestWasAlreadyTakenByAdv1(guild, adv1, adv2)
           guild == guildAdv[1]
           adv == guildAdv[3]
       IN /\ adventurersState' = [adventurersState EXCEPT ![adv] = <<"looking-for-quest", "">>]
          /\ UNCHANGED guildsState
          
AdventurerFinishesTheQuest ==
    /\ \E <<guild, adv>> \in GUILDS \X ADVENTURERS : QuestInProgress(guild, adv)
    /\ LET guildAdv == CHOOSE <<guild, adv>> \in GUILDS \X ADVENTURERS : QuestInProgress(guild, adv)
           guild == guildAdv[1]
           adv == guildAdv[2]
       IN /\ adventurersState' = [adventurersState EXCEPT ![adv] = <<"looking-for-quest", "">>]
          /\ guildsState' = [guildsState EXCEPT ![guild] = <<"completed", "">>]
    
Next ==
    \/ AdventurerConsidersAQuest
    \/ GuildCommitsToAnAdventurer
    \/ AdventurerCommitsToAGuild
    \/ AdventurerFinishesTheQuest
    \/ AdventurerDropsTakenQuest

Spec ==
    Init /\ [][Next]_<<guildsState, adventurersState>>
    
Consistent ==
    /\ \A <<guild, adv>> \in GUILDS \X ADVENTURERS : 
        /\ GuildIsCommittedWithAdventurer(guild, adv) => ( AdventurerIsCommittedWithGuild(guild, adv) \/ AdventurerIsConsideringGuild(guild, adv) )
        /\ AdventurerIsCommittedWithGuild(guild, adv) => GuildIsCommittedWithAdventurer(guild, adv)
    /\ \A <<adv1, adv2, guild>> \in ADVENTURERS \X ADVENTURERS \X GUILDS :
        ~ AreCommitted(guild, adv1) \/ ~ AreCommitted(guild, adv2) \/ adv1 = adv2

----------------------------------------------------------------------------

THEOREM Spec => [](TypeOk /\ Consistent)
    
=============================================================================
\* Modification History
\* Last modified Mon Sep 09 16:41:00 CEST 2019 by atfm0
\* Created Thu Sep 05 16:24:49 CEST 2019 by atfm0
