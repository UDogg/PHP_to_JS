<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class ClaimRaise extends Model
{
    protected $table = "claim_raise";
    protected $fillable = [
        'user_id',
        'workShopName',
        'lsoCode',
        'workshopAddress',
        'workshopEmail',
        'workShopContact',
        'workshopState',
        'workshopCity',
        'contactState',
        'contactCity',
        'contactPincode',
        'driverName',
        'insurerAddress',
        'customerEmailId',
        'customerMobileNo',
        'mobileNo',
        'intimatedName',
        'claimIntimatedBy',
        'descriptionOfAccident',
        'catastrophicCode',
        'partOfVehicle',
        'dateOfAccident',
        'placeOfAccident',
        'accidentState',
        'accidentCity',
        'accidentCityPincode',
        'natureOfAccident',
        'option',
        'wasVehicleParked',
        'authorizedDealer',
        'dealer',
        'claim_status',
        'claim_created_by',
        'reference_code',
        'mongoId',
        'policyNo',
        'registrationNo',
        'claim_number'
    ];
}
