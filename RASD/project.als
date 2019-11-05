sig Username{}

sig Password{}

sig Name{}

sig Surname{}

sig AuthenticatorID{}

sig FiscalCode{}

sig City{}

sig BirthLocation extends City{}

sig Address{}

sig PhoneNumber{}

sig DigitalCertificateX509{}

sig ViolationType{}

sig LicensePlate{}

sig Position{}

sig Note{}

sig Image{}

sig Date{ 
    day : one Int,
    month : one Int,
    year : one Int
}

sig TimeStamp extends Date {
    milliseconds : Int
}

sig Authorization {
    digitalCertificateX509 : one DigitalCertificateX509
}

sig Authentication {
    username : one Username,
    password : one Password
}

abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication
}

sig NormalUser extends User {
    reliabilityScore : one Int,
    date : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one BirthLocation,
    phoneNumber : one PhoneNumber,
    city : one City,
    address : one Address
}

sig Authority extends User {
    authorization : one Authorization
}

sig Violation {
    violationType : some ViolationType,
    image : one Image,
    licensePlate : one LicensePlate,
    quality : one Int,
    position : one Position,
    timeStamp : one TimeStamp,
    note : one Note,
    autheticatorID : one AuthenticatorID
} {#violationType <= 3 && # violationType >= 1}