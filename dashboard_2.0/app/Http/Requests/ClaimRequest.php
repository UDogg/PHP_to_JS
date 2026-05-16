<?php

namespace App\Http\Requests;

use Illuminate\Foundation\Http\FormRequest;

class ClaimRequest extends FormRequest
{
    /**
     * Determine if the user is authorized to make this request.
     */
    public function authorize(): bool
    {
        return true;
    }

    /**
     * Get the validation rules that apply to the request.
     *
     * @return array<string, \Illuminate\Contracts\Validation\ValidationRule|array<mixed>|string>
     */
    public function rules(): array
    {
        return [
            'natureOfAccident'      => 'required|string|max:255',
            'option'                => 'required|string|max:255', 
            'accidentCityPincode'   => 'required|string|max:10',  
            'accidentState'         => 'required|string|max:255',
            'accidentCity'          => 'required|string|max:255',
            'placeOfAccident'       => 'required|string|max:255',
            'dateOfAccident'        => 'required|date', 
            'partOfVehicle' => 'nullable|array', 
            'partOfVehicle.*' => 'string',  
            'descriptionOfAccident' => 'required|string|max:1000', 
            'claimIntimatedBy'      => 'required|string|max:255',
            'intimatedName'         => 'required|string|max:255',
            'mobileNo'              => 'required|numeric|digits_between:10,15', 
            'customerMobileNo'      => 'required|numeric|digits_between:10,15',
            'insurerAddress'        => 'required|string|max:255', 
            'contactState'          => 'required|string|max:255',
            'contactCity'           => 'required|string|max:255',
            'contactPincode'        => 'required|string|max:10',
            'driverName'            => 'required|string|max:255',
            'workshopState'         => 'required|string|max:255',
            'workshopCity'          => 'required|string|max:255',
            'workShopName'          => 'required|string|max:255',
            'workShopContact'       => 'required|numeric|digits_between:10,15',
            'workshopEmail'         => 'required|email|max:255', 
            'workshopAddress'       => 'required|string|max:500',
            'lsoCode'               => 'required|string|max:255',
        ];
        
    }
}
