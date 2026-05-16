<?php

namespace App\Models;

// use Illuminate\Contracts\Auth\MustVerifyEmail;
use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Foundation\Auth\User as Authenticatable;
use Illuminate\Notifications\Notifiable;
use Illuminate\Database\Eloquent\SoftDeletes;
use Laravel\Sanctum\HasApiTokens;
use Spatie\Activitylog\LogOptions;
use Spatie\Activitylog\Traits\LogsActivity;
use Spatie\Permission\Models\Role;
use Spatie\Permission\Traits\HasRoles;
use Illuminate\Foundation\Auth\Access\Authorizable;
class User extends Authenticatable
{
    use HasFactory, Notifiable, LogsActivity;
    use SoftDeletes, HasApiTokens;
    use HasRoles,Authorizable;
    protected $dates = ['deleted_at'];

    protected $guard_name = 'sanctum'; // Set correct guard

    /**
     * The attributes that are mass assignable.
     *
     * @var array<int, string>
     */
    protected $fillable = [
        'username',
        'name',
        'email',
        'mobile',
        'otp_sent_at',
        'gender',
        'address',
        'pincode',
        'status',
        'password',
        'otp',
        'otp_type',
        'confirm_otp',
        'totp_secret',
        'usertype',
        'reportingto',
        'zone_id',
        'pan_no',
        'adhar_no',
        'dob',
        'license_start_date',
        'license_end_date',
        'middle_name',
        'last_name',
        'qualification',
        'Is_delegate',
        'delegate_count',
        'employee_code',
        'pos_code',
        'share_code',
        'oemId',         
        'mispId',        
        'branchId',   
        'account_holder_name',
        'account_no',
        'ifsc_code',
        'bank_name',
        'bank_city',
        'bank_branch',  
        'is_b2cflag',
        'data_flag',
        'otp_expires_at',
        'list_flag',
        'lockout_time',
        'failed_login_attempts',
        'deleted_at',
        'path'
    ];
    protected $logAttributes = [
        'username',
        'name',
        'email',
        'mobile',
        'gender',
        'address',
        'pincode',
        'status',
        'password',
        'otp',
        'otp_type',
        'confirm_otp',
        'totp_secret',
        'usertype',
        'reportingto',
        'zone_id',
        'path'
    ];

    /**
     * The attributes that should be hidden for serialization.
     *
     * @var array<int, string>
     */
    protected $hidden = [
        'password',
        'remember_token',
    ];
    /**
     * Get the attributes that should be cast.
     *
     * @return array<string, string>
     */
    protected function casts(): array
    {
        return [
            'email_verified_at' => 'datetime',
            'password' => 'hashed',
            'otp_sent_at' => 'datetime',
        ];
    }
        public function lobs()
    {
        return $this->belongsToMany(lobMaster::class, 'user_lob_relation', 'user_id', 'lob_id');
    }
   public function getLevelAttribute(): int
    {
        return $this->path ? substr_count($this->path, '/') : 0;
    }
    public function scopeDescendantsOf($query, User $emp)
    {
        return $query->where('path', 'like', $emp->path . '/%');
    }
    public function scopeChildrenOf($query, User $emp)
    {
        return $query->where('path', 'like', $emp->path . '/%')
            ->whereRaw(
                "LENGTH(path) - LENGTH(REPLACE(path, '/', '')) = ?",
                [$emp->level + 1]
            );
    }
    public function getActivitylogOptions(): LogOptions
    {
        return LogOptions::defaults()
        ->logAll();
    }
    public function userType()
    {
        return $this->belongsTo(userTypes::class, 'usertype');
    }
    public function parent()
    {
        return $this->belongsTo(User::class, 'reportingto');
    }

    // Define a relationship to get child roles
    public function children($userType = null)
    {
    return $this->hasMany(User::class, 'reportingto')->when($userType, function ($query) use ($userType) {
        $query->where('userType', $userType);
    });
    }
    public function userMappings()
    {
        return $this->hasMany(UserMapping::class, 'user_id');
    }
    public function userRoles()
    {
        return $this->belongsToMany(Role::class, 'model_has_roles', 'model_id', 'role_id')
                    ->withPivot('model_type'); // if you need the model_type
    }

    public function userAdditionalData()
    {
        return $this->hasOne(UserAdditionalData::class, 'user_id','id');
    }
    public function userBranchRelation()
    {
        return $this->belongsToMany(AuBranch::class, 'user_branch_relation','user_id', 'branch_id','id','BranchID');
    }  

    public function reportingToUser()
    {
        return $this->belongsTo(User::class, 'reportingto', 'id');
    }

    public function mappedUser()
    {
        return $this->hasOne(User::class, 'employee_code', 'employee_code')
                    ->whereColumn('users.id', '!=', 'users.id');
    }

    public function userZoneRelation()
    {
        return $this->belongsTo(ZoneMasterModel::class, 'zone_id','id');
    }

    public function userQualificationRelation()
    {
        return $this->belongsTo(QualificationMaster::class, 'qualification','qualification_master_id');
    }
}
