<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Model;

class PaymentStatus extends Model
{
    protected $table = 'payment_status';
    protected $fillable = [
        'agent_id',
        'customer_id',
        'enquiry_id',
        'product_code',
        'payable_amount',
        'pg_additional_data',
        'payment_status',
        'transaction_id',
        'transaction_status',
        'payment_failure_reason',
        'call_back_additional_data',
        'lob_id',
        'data_push',
        'session_id',
        'resumed_journey_session_id'
    ];
}
