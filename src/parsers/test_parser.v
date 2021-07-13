Require Import List String.
Require Import Oqarina.parsers.aadl_lexer.
Require Import Oqarina.parsers.aadl_frontend.
Open Scope string_scope.

Definition example := "system s_impl_Instance : test_1::s.impl {
	system test_1::sc sc1 : test_1::s.impl:sc1 {}
}".
Compute (aadl_lexer.lex_string example).
Compute (string2aadl example).

Definition example2 :=
  "system PING_Native_Instance : PING_Package::PING.Native {
    bus Buses::Ethernet::Ethernet.impl the_bus : PING_Package::PING.Native:the_bus {
    }
    device Native_Sockets::Native_Sockets.POHI_ADA Eth1 : PING_Package::PING.Native:Eth1 {
      in busAccess Eth : Buses::Ethernet::Generic_Ethernet:Eth
    }
    device Native_Sockets::Native_Sockets.POHI_ADA Eth2 : PING_Package::PING.Native:Eth2 {
      in busAccess Eth : Buses::Ethernet::Generic_Ethernet:Eth
    }
    process PING_Package::A.Impl Node_A : PING_Package::PING.Native:Node_A {
      out eventDataPort Out_Port : PING_Package::A:Out_Port
      thread Software::P.Impl Pinger : PING_Package::A.Impl:Pinger {
        out eventDataPort Data_Source : Software::P:Data_Source
      }
    }
    process PING_Package::B.Impl Node_B : PING_Package::PING.Native:Node_B {
      in eventDataPort In_Port : PING_Package::B:In_Port
      thread Software::Q.Impl Ping_Me : PING_Package::B.Impl:Ping_Me {
        in eventDataPort Data_Sink : Software::Q:Data_Sink
      }
    }
    processor PING_Package::the_processor CPU_A : PING_Package::PING.Native:CPU_A {
    }
    processor PING_Package::the_processor CPU_B : PING_Package::PING.Native:CPU_B {
    }
  }".

Compute (aadl_lexer.lex_string example2).
Compute (string2aadl example2).
