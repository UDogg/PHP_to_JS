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
        Schema::create('policy_status_column_relation_masters', function (Blueprint $table) {
            $table->id();
            $table->string('column_id');
            $table->string('user_id');
            $table->string('role_id');
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->boolean('pin')->default(0);
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('policy_status_column_relation_masters');
    }
};
