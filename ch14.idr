data Access = LoggedOut | LoggedIn
data PwdCheck = Correct | Incorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
     Password : String -> ShellCmd PwdCheck LoggedOut 
                                 (\check => case check of
                                                 Correct => LoggedIn
                                                 Incorrect => LoggedOut)
     Logout : ShellCmd () LoggedIn (const LoggedOut)
     GetSecret : ShellCmd String LoggedIn (const LoggedIn)
     
     PutStr : String -> ShellCmd () state (const state)
     Pure : (res :ty) -> ShellCmd ty (s_fn res) s_fn
     (>>=) : ShellCmd a s1 s2_fn -> 
            ((res : a) -> ShellCmd b (s2_fn res) s3_fn) ->
            ShellCmd b s1 s3_fn

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wurzel" | Incorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret code: " ++ show msg ++ "\n")
             Logout
{-
sessionBad : ShellCmd () LoggedOut (const LoggedOut)
sessionBad = do Password "wurzel"
                msg <- GetSecret
                PutStr ("Secret code: " ++ show msg ++ "\n")
                Logout


noLogout : ShellCmd () LoggedOut (const LoggedOut)
noLogout = do Correct <- Password "wurzel" | Incorrect => PutStr "Wrong password"
              msg <- GetSecret
              PutStr ("Secret code: " ++ show msg ++ "\n")

-}
