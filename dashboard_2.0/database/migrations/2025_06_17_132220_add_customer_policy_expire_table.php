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
        if (!Schema::hasTable('customer_policy_expire')) {
            Schema::create('customer_policy_expire', function (Blueprint $table) {
                $table->id();
                $table->integer('customer_id');
                $table->integer('lob_id');
                $table->string('mobile_no')->nullable();
                $table->string('policy_no')->nullable();
                $table->date('policy_end_date')->nullable();
                $table->timestamps();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('customer_policy_expire');
    }
};
