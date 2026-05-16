<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        //
        if(!Schema::hasTable('users'))
        {
            Schema::table('users', function (Blueprint $table) {
               $table->string('dob',12)->nullable(); 
               $table->license_start_date('date')->nullable()->comment('pos license start date');
               $table->license_end_date('date')->nullable()->comment('pos license expiry date');
               $table->string('pos_code',50)->nullable()->comment('code')->comment('Employee or pos code based on usertype');
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
    }
};
