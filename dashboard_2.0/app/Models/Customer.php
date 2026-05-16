<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;
use Spatie\Permission\Traits\HasRoles;
use Laravel\Sanctum\HasApiTokens;


use Illuminate\Foundation\Auth\User as Authenticatable;

class Customer extends Authenticatable
{
    use HasFactory,HasApiTokens,HasRoles;

    protected $table = 'customers'; 

    protected $primaryKey = 'id'; 

    protected $gurd_name='customer';

    public $timestamps = false; // Since only `updated_at` is present, disable default timestamps

    protected $fillable = [
        'first_name',
        'middle_name',
        'last_name',
        'gender',
        'dob',
        'email',
        'password',
        'mobile',
        'name',
        'username',
        'address',
        'city',
        'state',
        'pincode',
        'company',
        'activation_code',
        'activated',
        'eia_no',
        'status',
        'eia_status',
        'source',
        'otp',
        'otp_count',
        'otp_sent_at',
        'otp_expiry',
        'annual_income',
        'marital_status',
        'country',
        'document_otp',
        'profile_status',
        'role_id',
        'usertype',
        'lockout_time',
        'failed_login_attempts',
    ];

    protected $casts = [
        'dob' => 'date',
        'otp_code' => 'integer',
        'otp_count' => 'integer',
        'document_otp' => 'integer',
    ];

    /**
     * Insert customer data into the database.
     *
     * @param array $data
     * @return Customer
     */
    public static function insertCustomer($data)
    {
        return self::create($data);
    }
    public function userRoles()
    {
        return $this->belongsToMany(Role::class, 'model_has_roles', 'model_id', 'role_id');
    }
}
